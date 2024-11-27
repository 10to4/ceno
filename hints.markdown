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

Like in SP1, the typed `read` is implemented inside the guest on top of `read_slice`: it's just a wrapper that deals with deserialisation for you.  In SP1 it's [implemented exactly how you'd expect](https://docs.rs/sp1-lib/3.3.0/src/sp1_lib/io.rs.html#87).  The same for us:

```rust
pub fn read<'a, T>(&'a mut self) -> &'b T
where
    T: Portable + for<'c> CheckBytes<HighValidator<'c, Error>>,
{
    rkyv::access::<T, Error>(self.read_slice()).unwrap()
}
```

> Sidenote: users who don't like `rkyv` can wrap their own favourite deserialiser around `read_slice`.  Just like we used `rkyv` in `sproll`, even though SP1 uses `bincode` natively.

`read_slice` is a bit more involved:

At the start of the [memory-mapped region for hints](https://github.com/scroll-tech/ceno/pull/457) we store information that lets us find the byte slice for each of the items we want to read.  We keep a mutable index to the next item to read, and we increment it each time `read_slice` is called.  We then return the byte slice for that item.

> Avid readers will notice that we essentially deserialise twice.  The original design used `rkyv` for both layers, but now we code up the outer layer by hand, mostly because rkyv would prefer to pin the end of the buffer to a fixed known location, but our VM design prefers to pin the start of the buffer.

Another technical note: in general our memory-mapped-io region will be larger than the buffer `rkvy` needs for its serialised data.  In that case, we will conceptually add arbitrary padding (eg all zeroes) to the end of the buffer.

> Sidenote: SP1 mixes general RAM and memory-mapped-io.  For that reason, they need some extra system calls (like `hint_len`) to tell the difference.  We don't have that problem, so we can keep things simpler.  This also has the benefit of only using functionality we already implemented for our VM.

Our design assumes that the memory-mapped-io region is read-only.  That's a good idea for both performance and security anyway, but we can also tweak the design slightly to support read-write backing storage.
