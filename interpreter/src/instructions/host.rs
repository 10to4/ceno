use crate::{
    gas::{self, COLD_ACCOUNT_ACCESS_COST, WARM_STORAGE_READ_COST},
    interpreter::{Interpreter, InterpreterAction},
    primitives::{Address, Bytes, Spec, SpecId::*, B256, U256},
    CallContext, CallInputs, CallScheme, CreateInputs, CreateScheme, Host, InstructionResult,
    Transfer, MAX_INITCODE_SIZE,
};
use alloc::{boxed::Box, vec::Vec};
use core::cmp::min;
use goldilocks::SmallField;
use revm_primitives::BLOCK_HASH_HISTORY;

pub fn balance<H: Host, F: SmallField, SPEC: Spec>(interpreter: &mut Interpreter<F>, host: &mut H) {
    pop_address!(interpreter, address);
    let Some((balance, is_cold)) = host.balance(address) else {
        interpreter.instruction_result = InstructionResult::FatalExternalError;
        host.record(&interpreter.generate_record(&Vec::new(), &Vec::new()));
        return;
    };
    gas!(
        interpreter,
        if SPEC::enabled(ISTANBUL) {
            // EIP-1884: Repricing for trie-size-dependent opcodes
            gas::account_access_gas::<SPEC>(is_cold)
        } else if SPEC::enabled(TANGERINE) {
            400
        } else {
            20
        }
    );
    push!(interpreter, balance);
    let operands = vec![balance];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

/// EIP-1884: Repricing for trie-size-dependent opcodes
pub fn selfbalance<H: Host, F: SmallField, SPEC: Spec>(
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    check!(interpreter, ISTANBUL);
    gas!(interpreter, gas::LOW);
    let Some((balance, _)) = host.balance(interpreter.contract.address) else {
        interpreter.instruction_result = InstructionResult::FatalExternalError;
        host.record(&interpreter.generate_record(&Vec::new(), &Vec::new()));
        return;
    };
    push!(interpreter, balance);
    let operands = vec![balance];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

pub fn extcodesize<H: Host, F: SmallField, SPEC: Spec>(
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    pop_address!(interpreter, address);
    let Some((code, is_cold)) = host.code(address) else {
        interpreter.instruction_result = InstructionResult::FatalExternalError;
        host.record(&interpreter.generate_record(&Vec::new(), &Vec::new()));
        return;
    };
    if SPEC::enabled(BERLIN) {
        gas!(
            interpreter,
            if is_cold {
                COLD_ACCOUNT_ACCESS_COST
            } else {
                WARM_STORAGE_READ_COST
            }
        );
    } else if SPEC::enabled(TANGERINE) {
        gas!(interpreter, 700);
    } else {
        gas!(interpreter, 20);
    }

    push!(interpreter, U256::from(code.len()));
    let operands = vec![U256::from(code.len())];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

/// EIP-1052: EXTCODEHASH opcode
pub fn extcodehash<H: Host, F: SmallField, SPEC: Spec>(
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    check!(interpreter, CONSTANTINOPLE);
    pop_address!(interpreter, address);
    let Some((code_hash, is_cold)) = host.code_hash(address) else {
        interpreter.instruction_result = InstructionResult::FatalExternalError;
        host.record(&interpreter.generate_record(&Vec::new(), &Vec::new()));
        return;
    };
    if SPEC::enabled(BERLIN) {
        gas!(
            interpreter,
            if is_cold {
                COLD_ACCOUNT_ACCESS_COST
            } else {
                WARM_STORAGE_READ_COST
            }
        );
    } else if SPEC::enabled(ISTANBUL) {
        gas!(interpreter, 700);
    } else {
        gas!(interpreter, 400);
    }
    push_b256!(interpreter, code_hash);
    let operands = vec![
        U256::try_from(address.into_word()).unwrap(),
        U256::try_from(code_hash).unwrap(),
    ];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

pub fn extcodecopy<H: Host, F: SmallField, SPEC: Spec>(
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    pop_address!(interpreter, address);
    pop!(interpreter, memory_offset, code_offset, len_u256);

    let Some((code, is_cold)) = host.code(address) else {
        interpreter.instruction_result = InstructionResult::FatalExternalError;
        return;
    };

    let len = as_usize_or_fail!(interpreter, len_u256.0);
    gas_or_fail!(
        interpreter,
        gas::extcodecopy_cost::<SPEC>(len as u64, is_cold)
    );
    if len == 0 {
        return;
    }
    let memory_offset = as_usize_or_fail!(interpreter, memory_offset.0);
    let code_offset = min(as_usize_saturated!(code_offset.0), code.len());
    shared_memory_resize!(interpreter, memory_offset, len);

    // Note: this can't panic because we resized memory to fit.
    interpreter.shared_memory.set_data(
        memory_offset,
        code_offset,
        len,
        code.bytes(),
        interpreter.memory_timestamp,
    );
    let operands = vec![
        U256::try_from(address.into_word()).unwrap(),
        U256::from(memory_offset),
        U256::from(code_offset),
        len_u256.0,
    ];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

pub fn blockhash<H: Host, F: SmallField>(interpreter: &mut Interpreter<F>, host: &mut H) {
    gas!(interpreter, gas::BLOCKHASH);
    pop_top!(interpreter, number);

    if let Some(diff) = host.env().block.number.checked_sub(*number.0) {
        let diff = as_usize_saturated!(diff);
        // blockhash should push zero if number is same as current block number.
        if diff <= BLOCK_HASH_HISTORY && diff != 0 {
            let Some(hash) = host.block_hash(*number.0) else {
                interpreter.instruction_result = InstructionResult::FatalExternalError;
                host.record(&interpreter.generate_record(&Vec::new(), &Vec::new()));
                return;
            };
            *number.0 = U256::from_be_bytes(hash.0);
            *number.1 = interpreter.stack_timestamp;
            let operands = vec![*number.0];
            host.record(&interpreter.generate_record(&operands, &Vec::new()));
            return;
        }
    }
    *number.0 = U256::ZERO;
    *number.1 = interpreter.stack_timestamp;
    let operands = vec![*number.0];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

pub fn sload<H: Host, F: SmallField, SPEC: Spec>(interpreter: &mut Interpreter<F>, host: &mut H) {
    pop!(interpreter, index);

    let Some((value, is_cold)) = host.sload(interpreter.contract.address, index.0) else {
        interpreter.instruction_result = InstructionResult::FatalExternalError;
        host.record(&interpreter.generate_record(&Vec::new(), &Vec::new()));
        return;
    };
    gas!(interpreter, gas::sload_cost::<SPEC>(is_cold));
    push!(interpreter, value);
    let operands = vec![index.0, value];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

pub fn sstore<H: Host, F: SmallField, SPEC: Spec>(interpreter: &mut Interpreter<F>, host: &mut H) {
    check_staticcall!(interpreter);

    pop!(interpreter, index, value);
    let Some((original, old, new, is_cold)) =
        host.sstore(interpreter.contract.address, index.0, value.0)
    else {
        interpreter.instruction_result = InstructionResult::FatalExternalError;
        host.record(&interpreter.generate_record(&Vec::new(), &Vec::new()));
        return;
    };
    gas_or_fail!(interpreter, {
        let remaining_gas = interpreter.gas.remaining();
        gas::sstore_cost::<SPEC>(original, old, new, remaining_gas, is_cold)
    });
    refund!(interpreter, gas::sstore_refund::<SPEC>(original, old, new));
    let operands = vec![index.0, value.0];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

/// EIP-1153: Transient storage opcodes
/// Store value to transient storage
pub fn tstore<H: Host, F: SmallField, SPEC: Spec>(interpreter: &mut Interpreter<F>, host: &mut H) {
    check!(interpreter, CANCUN);
    check_staticcall!(interpreter);
    gas!(interpreter, gas::WARM_STORAGE_READ_COST);

    pop!(interpreter, index, value);

    host.tstore(interpreter.contract.address, index.0, value.0);
    let operands = vec![index.0, value.0];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

/// EIP-1153: Transient storage opcodes
/// Load value from transient storage
pub fn tload<H: Host, F: SmallField, SPEC: Spec>(interpreter: &mut Interpreter<F>, host: &mut H) {
    check!(interpreter, CANCUN);
    gas!(interpreter, gas::WARM_STORAGE_READ_COST);

    pop_top!(interpreter, index);

    *index.0 = host.tload(interpreter.contract.address, *index.0);
    let operands = vec![*index.0];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

pub fn log<const N: usize, H: Host, F: SmallField>(interpreter: &mut Interpreter<F>, host: &mut H) {
    check_staticcall!(interpreter);

    pop!(interpreter, offset, len);
    let len = as_usize_or_fail!(interpreter, len.0);
    gas_or_fail!(interpreter, gas::log_cost(N as u8, len as u64));
    let data = if len == 0 {
        Bytes::new()
    } else {
        let offset = as_usize_or_fail!(interpreter, offset.0);
        shared_memory_resize!(interpreter, offset, len);
        Bytes::copy_from_slice(interpreter.shared_memory.slice(offset, len).0)
    };

    if interpreter.stack.len() < N {
        interpreter.instruction_result = InstructionResult::StackUnderflow;
        return;
    }

    let mut topics = Vec::with_capacity(N);
    for _ in 0..N {
        // SAFETY: stack bounds already checked few lines above
        topics.push(B256::from(unsafe { interpreter.stack.pop_unsafe().0 }));
    }

    let mut operands = vec![offset.0, U256::from(len)];
    operands.extend(topics.iter().map(|x| U256::try_from(*x).unwrap()));
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
    host.log(interpreter.contract.address, topics, data);
}

pub fn selfdestruct<H: Host, F: SmallField, SPEC: Spec>(
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    check_staticcall!(interpreter);
    pop_address!(interpreter, target);

    let Some(res) = host.selfdestruct(interpreter.contract.address, target) else {
        interpreter.instruction_result = InstructionResult::FatalExternalError;
        return;
    };

    // EIP-3529: Reduction in refunds
    if !SPEC::enabled(LONDON) && !res.previously_destroyed {
        refund!(interpreter, gas::SELFDESTRUCT)
    }
    gas!(interpreter, gas::selfdestruct_cost::<SPEC>(res));

    interpreter.instruction_result = InstructionResult::SelfDestruct;
    let operands = vec![U256::try_from(target.into_word()).unwrap()];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));
}

pub fn create<const IS_CREATE2: bool, H: Host, F: SmallField, SPEC: Spec>(
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    check_staticcall!(interpreter);

    // EIP-1014: Skinny CREATE2
    if IS_CREATE2 {
        check!(interpreter, PETERSBURG);
    }

    pop!(interpreter, value, code_offset, len);
    let len = as_usize_or_fail!(interpreter, len.0);

    let mut code = Bytes::new();
    if len != 0 {
        // EIP-3860: Limit and meter initcode
        if SPEC::enabled(SHANGHAI) {
            // Limit is set as double of max contract bytecode size
            let max_initcode_size = host
                .env()
                .cfg
                .limit_contract_code_size
                .map(|limit| limit.saturating_mul(2))
                .unwrap_or(MAX_INITCODE_SIZE);
            if len > max_initcode_size {
                interpreter.instruction_result = InstructionResult::CreateInitCodeSizeLimit;
                return;
            }
            gas!(interpreter, gas::initcode_cost(len as u64));
        }

        let code_offset = as_usize_or_fail!(interpreter, code_offset.0);
        shared_memory_resize!(interpreter, code_offset, len);
        code = Bytes::copy_from_slice(interpreter.shared_memory.slice(code_offset, len).0);
    }

    let mut operands = vec![value.0, code_offset.0, U256::from(len)];
    // EIP-1014: Skinny CREATE2
    let scheme = if IS_CREATE2 {
        pop!(interpreter, salt);
        operands.push(salt.0);
        gas_or_fail!(interpreter, gas::create2_cost(len));
        CreateScheme::Create2 { salt: salt.0 }
    } else {
        gas!(interpreter, gas::CREATE);
        CreateScheme::Create
    };

    host.record(&interpreter.generate_record(&operands, &Vec::new()));

    let mut gas_limit = interpreter.gas().remaining();

    // EIP-150: Gas cost changes for IO-heavy operations
    if SPEC::enabled(TANGERINE) {
        // take remaining gas and deduce l64 part of it.
        gas_limit -= gas_limit / 64
    }
    gas!(interpreter, gas_limit);

    // Call host to interact with target contract
    interpreter.next_action = Some(InterpreterAction::Create {
        inputs: Box::new(CreateInputs {
            caller: interpreter.contract.address,
            scheme,
            value: value.0,
            init_code: code,
            gas_limit,
        }),
    });
    interpreter.instruction_result = InstructionResult::CallOrCreate;
}

pub fn call<H: Host, F: SmallField, SPEC: Spec>(interpreter: &mut Interpreter<F>, host: &mut H) {
    call_inner::<SPEC, H, F>(CallScheme::Call, interpreter, host);
}

pub fn call_code<H: Host, F: SmallField, SPEC: Spec>(
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    call_inner::<SPEC, H, F>(CallScheme::CallCode, interpreter, host);
}

pub fn delegate_call<H: Host, F: SmallField, SPEC: Spec>(
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    call_inner::<SPEC, H, F>(CallScheme::DelegateCall, interpreter, host);
}

pub fn static_call<H: Host, F: SmallField, SPEC: Spec>(
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    call_inner::<SPEC, H, F>(CallScheme::StaticCall, interpreter, host);
}

pub fn call_inner<SPEC: Spec, H: Host, F: SmallField>(
    scheme: CallScheme,
    interpreter: &mut Interpreter<F>,
    host: &mut H,
) {
    match scheme {
        // EIP-7: DELEGATECALL
        CallScheme::DelegateCall => check!(interpreter, HOMESTEAD),
        // EIP-214: New opcode STATICCALL
        CallScheme::StaticCall => check!(interpreter, BYZANTIUM),
        _ => (),
    }

    pop!(interpreter, local_gas_limit);
    pop_address!(interpreter, to);
    // max gas limit is not possible in real ethereum situation.
    // But for tests we would not like to fail on this.
    // Gas limit for subcall is taken as min of this value and current gas limit.
    let local_gas_limit = u64::try_from(local_gas_limit.0).unwrap_or(u64::MAX);

    let value = match scheme {
        CallScheme::CallCode => {
            pop!(interpreter, value);
            value.0
        }
        CallScheme::Call => {
            pop!(interpreter, value);
            if interpreter.is_static && value.0 != U256::ZERO {
                interpreter.instruction_result = InstructionResult::CallNotAllowedInsideStatic;
                return;
            }
            value.0
        }
        CallScheme::DelegateCall | CallScheme::StaticCall => U256::ZERO,
    };

    pop!(interpreter, in_offset, in_len, out_offset, out_len);

    let operands = vec![
        U256::from(local_gas_limit),
        U256::try_from(to.into_word()).unwrap(),
        in_offset.0,
        in_len.0,
        out_offset.0,
        out_len.0,
    ];
    host.record(&interpreter.generate_record(&operands, &Vec::new()));

    let in_len = as_usize_or_fail!(interpreter, in_len.0);
    let input = if in_len != 0 {
        let in_offset = as_usize_or_fail!(interpreter, in_offset.0);
        shared_memory_resize!(interpreter, in_offset, in_len);
        Bytes::copy_from_slice(interpreter.shared_memory.slice(in_offset, in_len).0)
    } else {
        Bytes::new()
    };

    let out_len = as_usize_or_fail!(interpreter, out_len.0);
    let out_offset = if out_len != 0 {
        let out_offset = as_usize_or_fail!(interpreter, out_offset.0);
        shared_memory_resize!(interpreter, out_offset, out_len);
        out_offset
    } else {
        usize::MAX //unrealistic value so we are sure it is not used
    };

    let context = match scheme {
        CallScheme::Call | CallScheme::StaticCall => CallContext {
            address: to,
            caller: interpreter.contract.address,
            code_address: to,
            apparent_value: value,
            scheme,
        },
        CallScheme::CallCode => CallContext {
            address: interpreter.contract.address,
            caller: interpreter.contract.address,
            code_address: to,
            apparent_value: value,
            scheme,
        },
        CallScheme::DelegateCall => CallContext {
            address: interpreter.contract.address,
            caller: interpreter.contract.caller,
            code_address: to,
            apparent_value: interpreter.contract.value,
            scheme,
        },
    };

    let transfer = match scheme {
        CallScheme::Call => Transfer {
            source: interpreter.contract.address,
            target: to,
            value,
        },
        CallScheme::CallCode => Transfer {
            source: interpreter.contract.address,
            target: interpreter.contract.address,
            value,
        },
        _ => {
            //this is dummy send for StaticCall and DelegateCall, it should do nothing and dont touch anything.
            Transfer {
                source: interpreter.contract.address,
                target: interpreter.contract.address,
                value: U256::ZERO,
            }
        }
    };

    // load account and calculate gas cost.
    let Some((is_cold, exist)) = host.load_account(to) else {
        interpreter.instruction_result = InstructionResult::FatalExternalError;
        return;
    };
    let is_new = !exist;

    gas!(
        interpreter,
        gas::call_cost::<SPEC>(
            value != U256::ZERO,
            is_new,
            is_cold,
            matches!(scheme, CallScheme::Call | CallScheme::CallCode),
            matches!(scheme, CallScheme::Call | CallScheme::StaticCall),
        )
    );

    // EIP-150: Gas cost changes for IO-heavy operations
    let mut gas_limit = if SPEC::enabled(TANGERINE) {
        let gas = interpreter.gas().remaining();
        // take l64 part of gas_limit
        min(gas - gas / 64, local_gas_limit)
    } else {
        local_gas_limit
    };

    gas!(interpreter, gas_limit);

    // add call stipend if there is value to be transferred.
    if matches!(scheme, CallScheme::Call | CallScheme::CallCode) && transfer.value != U256::ZERO {
        gas_limit = gas_limit.saturating_add(gas::CALL_STIPEND);
    }
    let is_static = matches!(scheme, CallScheme::StaticCall) || interpreter.is_static;

    // Call host to interact with target contract
    interpreter.next_action = Some(InterpreterAction::SubCall {
        inputs: Box::new(CallInputs {
            contract: to,
            transfer,
            input,
            gas_limit,
            context,
            is_static,
        }),
        return_memory_offset: out_offset..out_offset + out_len,
    });
    interpreter.instruction_result = InstructionResult::CallOrCreate;
}