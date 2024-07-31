use ff_ext::ExtensionField;

use crate::{
    structs_v2::{Circuit, CircuitBuilderV2},
    util_v2::{Expression, WitIn, ZKVMV2Error},
};
use ff::Field;

impl<E: ExtensionField> CircuitBuilderV2<E> {
    pub fn new() -> Self {
        Self {
            num_witin: 0,
            r_expressions: vec![],
            w_expressions: vec![],
            lk_expressions: vec![],
            assert_zero_expressions: vec![],
            assert_zero_sumcheck_expressions: vec![],
            chip_record_alpha: Expression::Challenge(0, 1, E::ONE, E::ZERO),
            chip_record_beta: Expression::Challenge(1, 1, E::ONE, E::ZERO),
            phantom: std::marker::PhantomData,
        }
    }

    pub fn create_witin(&mut self) -> WitIn {
        WitIn {
            id: {
                let id = self.num_witin;
                self.num_witin += 1;
                id
            },
        }
    }
    pub fn read_record(&mut self, rlc_record: Expression<E>) -> Result<(), ZKVMV2Error> {
        assert_eq!(
            rlc_record.degree(),
            1,
            "rlc record degree {} != 1",
            rlc_record.degree()
        );
        self.r_expressions.push(rlc_record);
        Ok(())
    }

    pub fn write_record(&mut self, rlc_record: Expression<E>) -> Result<(), ZKVMV2Error> {
        assert_eq!(
            rlc_record.degree(),
            1,
            "rlc record degree {} != 1",
            rlc_record.degree()
        );
        self.w_expressions.push(rlc_record);
        Ok(())
    }

    pub fn rlc_chip_record(&self, records: Vec<Expression<E>>) -> Expression<E> {
        assert!(!records.is_empty());
        let beta_pows = {
            let mut beta_pows = Vec::with_capacity(records.len());
            beta_pows.push(Expression::Constant(E::BaseField::ONE));
            (0..records.len() - 1).for_each(|_| {
                beta_pows.push(self.chip_record_beta.clone() * beta_pows.last().unwrap().clone())
            });
            beta_pows
        };

        let item_rlc = beta_pows
            .into_iter()
            .zip(records.iter())
            .map(|(beta, record)| beta * record.clone())
            .reduce(|a, b| a + b)
            .expect("reduce error");

        item_rlc + self.chip_record_alpha.clone()
    }

    pub fn require_zero(&mut self, assert_zero_expr: Expression<E>) -> Result<(), ZKVMV2Error> {
        assert!(
            assert_zero_expr.degree() > 0,
            "constant expression assert to zero ?"
        );
        if assert_zero_expr.degree() == 1 {
            self.assert_zero_expressions.push(assert_zero_expr);
        } else {
            // TODO check expression must be in multivariate monomial form
            self.assert_zero_sumcheck_expressions.push(assert_zero_expr);
        }
        Ok(())
    }

    pub fn require_equal(
        &mut self,
        target: Expression<E>,
        rlc_record: Expression<E>,
    ) -> Result<(), ZKVMV2Error> {
        self.require_zero(target - rlc_record)
    }

    pub fn require_one(&mut self, expr: Expression<E>) -> Result<(), ZKVMV2Error> {
        self.require_zero(Expression::from(1) - expr)
    }

    pub fn finalize_circuit(&self) -> Circuit<E> {
        Circuit {
            num_witin: self.num_witin,
            r_expressions: self.r_expressions.clone(),
            w_expressions: self.w_expressions.clone(),
            lk_expressions: self.lk_expressions.clone(),
            assert_zero_expressions: self.assert_zero_expressions.clone(),
            assert_zero_sumcheck_expressions: self.assert_zero_sumcheck_expressions.clone(),
        }
    }
}