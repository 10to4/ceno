use itertools::izip;
use rkyv::{
    Archive, Deserialize, Portable, Serialize,
    api::high::{HighSerializer, HighValidator},
    bytecheck::CheckBytes,
    rancor::Error,
    ser::allocator::ArenaHandle,
    to_bytes,
    util::AlignedVec,
};

#[derive(Default)]
pub struct CenoStdin {
    pub items: Vec<AlignedVec>,
}

impl CenoStdin {
    pub fn write_slice(&mut self, bytes: AlignedVec) {
        self.items.push(bytes);
    }
    pub fn write(
        &mut self,
        item: &impl for<'a> Serialize<HighSerializer<AlignedVec, ArenaHandle<'a>, Error>>,
    ) -> Result<(), Error> {
        let bytes = to_bytes::<Error>(item)?;
        self.write_slice(bytes);
        Ok(())
    }

    pub fn finalise(&self) -> AlignedVec {
        // TODO: perhaps don't hardcode 16 here.
        // It's from rkyv's format, so we can probably take it from there somehow?
        let initial_offset = (size_of::<u32>() * self.items.len()).next_multiple_of(16);
        println!("offset: {}", initial_offset);
        let offsets: Vec<u32> = self
            .items
            .iter()
            .scan(initial_offset, |acc, bytes| {
                let output = (*acc + bytes.len()) as u32;
                print!("len: {}\t", bytes.len());
                *acc += bytes.len().next_multiple_of(16);
                println!("acc: {}", *acc);
                Some(output)
            })
            .collect();
        let offsets_u8: Vec<u8> = offsets.iter().copied().flat_map(u32::to_le_bytes).collect();
        let mut buf: AlignedVec = AlignedVec::new();
        buf.extend_from_slice(&offsets_u8);
        println!("buf.len() after offsets: {}", buf.len());
        buf.extend_from_slice(&vec![0; buf.len().next_multiple_of(16) - buf.len()]);
        println!("buf.len() after offset padding: {}", buf.len());
        for (offset, item) in izip!(offsets, &self.items) {
            buf.extend_from_slice(item);
            buf.extend_from_slice(&vec![0; buf.len().next_multiple_of(16) - buf.len()]);
            assert_eq!(buf.len(), offset.next_multiple_of(16) as usize);
        }
        buf
    }
}

pub type CenoIter<'a> = std::slice::Iter<'a, rkyv::vec::ArchivedVec<u8>>;

pub fn read<'a, 'b, T>(iter: &'a mut impl Iterator<Item = &'b [u8]>) -> &'b T
where
    T: Portable + for<'c> CheckBytes<HighValidator<'c, Error>>,
{
    let bytes = iter.next().unwrap();
    rkyv::access::<T, Error>(bytes).unwrap()
}

// TODO: implement read_slice

#[derive(Archive, Deserialize, Serialize, Debug, PartialEq)]
#[rkyv(
    // This will generate a PartialEq impl between our unarchived
    // and archived types
    compare(PartialEq),
    // Derives can be passed through to the generated type:
    derive(Debug),
)]
struct Test {
    int: u32,
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
                int: 0xDEAD_BEEF,
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
        stdin.finalise()
    }

    /// The equivalent of this function would run in the guest.
    ///
    /// `buf` would be the memory mapped region for private hints.
    pub fn consume(buf: AlignedVec) {
        println!("\nConsuming...");
        let mut iter = {
            // TODO: hide this section in the SDK library, it wouldn't be exposed to the user.
            let (prefix, lengths, suffix) = unsafe { buf.align_to::<u32>() };
            assert!(prefix.is_empty());
            assert!(suffix.is_empty());
            lengths.iter().map(|len| {
                println!("len: {}", len);
                &buf[..*len as usize]
            })
        };

        // TODO: see if we can move `.next().unwrap()` into the `read` function, and still have a happy borrow checker.
        // (In the guest, this would be hidden behind a mutable static anyway.)
        // let test1 = read::<ArchivedTest>(iter.next().unwrap());
        let test1 = read::<ArchivedTest>(&mut iter);
        assert_eq!(test1, &Test {
            int: 0xDEAD_BEEF,
            string: "hello world".to_string(),
            option: Some(vec![1, 2, 3, 4]),
        });
        let number = read::<u8>(&mut iter);
        assert_eq!(number, &0xaf_u8);
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
