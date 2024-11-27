This is an elaboration on https://github.com/scroll-tech/ceno/discussions/551

# Guest's points of view

[Inspired by SP1](https://docs.succinct.xyz/writing-programs/inputs-and-outputs.html), we will give guests two functions to read unconstrained input (also knows as hints).  The first is `read`, which reads in a value of a given type.  The second is `read_slice`, which reads in a byte array.

```rust
pub fn read<T>() -> &'static T
where
    T: Portable + for<'a> CheckBytes<HighValidator<'a, rancor::Failure>>

pub fn read_slice() -> &'static [u8]
```

There are two main differences to SP1:
1. We are using `rkyv` instead of `bincode`.  That's because `rkyv` is a lot faster, and we are already using it in `sproll`.  The bounds on `T` in `read` [reflect that](https://docs.rs/rkyv/latest/rkyv/fn.access.html).
2. We are returning references instead of copied values.  That's because `rkyv` is zero-copy, and we want to take advantage of that.

Just like in SP1, the host has two corresponding functions to create that input: `write` and `write_slice`.  From the user's point of view, they work exactly like you imagine they would.

> Sidenote: in this model, the host has to prepare the input in exactly the order that the guest requests it.  That approach works well for simple examples.  If this inflexibility ever becomes a limiting factor, Matthias has a design to fix it.  But it's probably overkill, given that the in-order approach works well enough for SP1.

# Under the hood

Like in SP1, the typed `read` is implemented inside the guest on top of `read_slice`: it's just a wrapper that deals with deserialisation for you.  It's [implemented exactly how you'd expect](https://docs.rs/sp1-lib/3.3.0/src/sp1_lib/io.rs.html#87).

> Sidenote: users who don't like `rkyv` can wrap their own favourite deserialiser around `read_slice`.  Just like we used `rkyv` in `sproll`, even though SP1 uses `bincode` natively.

`read_slice` is a bit more involved: we treat the whole [memory-mapped-io region](https://github.com/scroll-tech/ceno/pull/457) as a single byte array that we feed to rkyv and zero-copy-deserialise it once at the start of the guest program, to get something like `ArchivedVec<&[u8]>`.  We then keep track of the current position in that array, and return the next item from it, when `read_slice` is called.  That is to say, we turn it into a Rust iterator, that's a mutable static behind the scenes, and we can get away with this because our guest programs are single threaded.  (The same assumption we (and Risc0 and SP1) use in our allocators.)

Avid readers will notice that we are deserialising our data twice.  Thanks to `rkyv`'s clever design, that doesn't cost us anything extra.

Another technical note: in general our memory-mapped-io region will be larger than the buffer `rkvy` needs for its serialised data.  In that case, we will conceptually add arbitrary padding (eg all zeroes) to the _front_ of the buffer. `rkyv` won't access that, so it will never show up in the execution record either. `rkyv` reads its 'root' from the back of the buffer and follows internal pointers to unravel the whole structure, so it will never see the padding.

> Sidenote: SP1 mixes general RAM and memory-mapped-io.  For that reason, they need some extra system calls (like `hint_len`) to tell the difference.  We don't have that problem, so we can keep things simpler.  This also has the benefit of only using functionality we already implemented for our VM.

Our design assumes that the memory-mapped-io region is read-only.  That's a good idea for both performance and security anyway, but we can also tweak the design slightly to support read-write backing storage.

> As an extra explanation: from the guest program's point of view, you can read an arbitrary number of hints during execution, but as far as the VM is concerned it's just one big hint. `rkyv` mediates between the two views, by converting from a single long byte slice to a collection of smaller (contained) slices.
