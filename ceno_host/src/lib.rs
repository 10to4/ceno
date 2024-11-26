#![feature(trivial_bounds)]
// TODO: create sp1 style host functionality.  Start with write and write_slice.

use rkyv::{
    Archive, Deserialize, Portable, Serialize,
    api::high::{HighSerializer, HighValidator},
    bytecheck::CheckBytes,
    rancor::Error,
    ser::allocator::ArenaHandle,
    to_bytes,
    util::AlignedVec,
};

#[derive(Archive, Deserialize, Serialize, Default)]
pub struct CenoStdin {
    pub items: Vec<Vec<u8>>,
}

impl CenoStdin {
    pub fn write_slice(&mut self, item: AlignedVec) {
        // Now the question is: are these bytes aligned enough?
        self.items.push(item.to_vec());
    }
    pub fn write(
        &mut self,
        item: &impl for<'a> Serialize<HighSerializer<AlignedVec, ArenaHandle<'a>, Error>>,
    ) -> Result<(), Error> {
        // consider expanding to 16 bytes alignment and left padding with zeroes and using into_boxed_slice?
        // Or perhaps write our own serialiser?
        let bytes = to_bytes::<Error>(item)?;
        self.items.push(bytes.to_vec());
        Ok(())
    }

    pub fn finalise(&self) -> Result<AlignedVec, Error> {
        to_bytes::<Error>(&self.items)
    }
}

type CenoIter<'a> = std::slice::Iter<'a, rkyv::vec::ArchivedVec<u8>>;

pub fn prepare(ArchivedCenoStdin { items }: &ArchivedCenoStdin) -> CenoIter<'_> {
    items.iter()
}

pub fn read<'a, T>(i: &mut CenoIter<'a>) -> &'a T
where
    T: Portable + for<'b> CheckBytes<HighValidator<'b, Error>>,
{
    let bytes = i.next().unwrap();
    rkyv::access::<T, Error>(bytes).unwrap()
}

pub fn read_slice<'a>(i: &mut CenoIter<'a>) -> &'a [u8] {
    let bytes = i.next().unwrap();
    bytes.as_slice()
}

#[derive(Archive, Deserialize, Serialize, Debug, PartialEq)]
#[rkyv(
    // This will generate a PartialEq impl between our unarchived
    // and archived types
    compare(PartialEq),
    // Derives can be passed through to the generated type:
    derive(Debug),
)]
struct Test {
    int: u8,
    string: String,
    option: Option<Vec<i32>>,
}

#[derive(Archive, Deserialize, Serialize, Debug, PartialEq)]
#[rkyv(
    // This will generate a PartialEq impl between our unarchived
    // and archived types
    compare(PartialEq),
    // Derives can be passed through to the generated type:
    derive(Debug),
)]
struct Toast {
    stuff: Option<Vec<String>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use rkyv::{
        deserialize,
        rancor::{Error, Failure},
        to_bytes,
        util::AlignedVec,
    };

    /// The equivalent of this function would run in the host.
    ///
    /// We create three different items, and show that we can read them back in `consume`.
    pub fn make_stdin() -> AlignedVec {
        let mut stdin = CenoStdin::default();
        stdin
            .write(&Test {
                int: 42,
                string: "hello world".to_string(),
                option: Some(vec![1, 2, 3, 4]),
            })
            .unwrap();
        stdin.write(&0xaf_u8).unwrap();
        stdin
            .write(&Toast {
                stuff: Some(vec!["hello scroll".to_string()]),
            })
            .unwrap();
        stdin.finalise().unwrap()
    }

    /// The equivalent of this function would run in the guest.
    ///
    /// `buf` would be the memory mapped region for private hints.
    pub fn consume(buf: AlignedVec) {
        let archived = rkyv::access::<ArchivedCenoStdin, Failure>(&buf[..]).unwrap();
        // This iterator would live in a mutable static behind the scenes,
        // so that we don't have to pass it around.
        let mut iter = prepare(archived);

        let test1 = read::<ArchivedTest>(&mut iter);
        assert_eq!(test1, &Test {
            int: 42,
            string: "hello world".to_string(),
            option: Some(vec![1, 2, 3, 4]),
        });
        let dead_beef = read::<u8>(&mut iter);
        assert_eq!(dead_beef, &0xaf_u8);
        let test2 = read::<ArchivedToast>(&mut iter);
        assert_eq!(test2, &Toast {
            stuff: Some(vec!["hello scroll".to_string()]),
        });
    }

    #[test]
    fn test_prepare_and_consume_items() {
        let stdin = make_stdin();
        consume(stdin);
    }

    #[test]
    fn test_rkyv_padding() {
        let value = Test {
            int: 42,
            string: "hello world".to_string(),
            option: Some(vec![1, 2, 3, 4]),
        };

        // Serializing is as easy as a single function call
        let bytes: AlignedVec = to_bytes::<Error>(&value).unwrap();

        {
            // Or you can customize your serialization for better performance or control
            // over resource usage
            use rkyv::{api::high::to_bytes_with_alloc, ser::allocator::Arena};

            let mut arena = Arena::new();
            let _bytes = to_bytes_with_alloc::<_, Error>(&value, arena.acquire()).unwrap();
        }
        // You can use the safe API for fast zero-copy deserialization
        let archived = rkyv::access::<ArchivedTest, Failure>(&bytes[..]).unwrap();
        assert_eq!(archived, &value);

        // And you can always deserialize back to the original type
        let deserialized = deserialize::<Test, Error>(archived).unwrap();
        assert_eq!(deserialized, value);

        let mut rng = rand::thread_rng();

        {
            // https://rkyv.org/format.html says:
            // This deterministic layout means that you don't need to store the position of
            // the root object in most cases. As long as your buffer ends right at the end of
            // your root object, you can use `access` with your buffer.

            // Thus left padding should work.  We add 1024 bytes of random junk to the left.

            let mut left_padded_bytes = vec![0; 1024];
            rng.fill(&mut left_padded_bytes[..]);
            // Then add our original bytes to the end:
            left_padded_bytes.extend_from_slice(&bytes);

            // we should be able to access as before:
            let archived2 = rkyv::access::<ArchivedTest, Error>(&left_padded_bytes[..]).unwrap();
            assert_eq!(archived2, &value);
        }
        {
            // The same but right padding junk should fail:
            let mut right_padded_bytes = bytes.clone();
            let mut junk = vec![0; 1024];
            rng.fill(&mut junk[..]);
            right_padded_bytes.extend_from_slice(&junk);
            // we should not be able to access as before:
            let _ = rkyv::access::<ArchivedTest, Error>(&right_padded_bytes[..])
                .expect_err("This should fail.");
        }
    }
}
