use std::convert::TryInto;
use std::io::{Read, Write};

use ed::{Encode, Decode, Terminated};
use failure::bail;

use super::{Op, Node};
use crate::tree::{HASH_LENGTH, Key, Value};
use crate::error::Result;

impl Encode for Op {
    fn encode_into<W: Write>(&self, dest: &mut W) -> ed::Result<()> {
        match self {
            Op::Push(Node::Hash(hash)) => {
                dest.write_all(&[ 0x01 ])?;
                dest.write_all(hash)?;
            },
            Op::Push(Node::KVHash(kv_hash)) => {
                dest.write_all(&[ 0x02 ])?;
                dest.write_all(kv_hash)?;
            },
            Op::Push(Node::KV(key, value)) => {
                debug_assert!(key.len() < 256);
                debug_assert!(value.len() < 65536);

                dest.write_all(&[
                    0x03,
                    key.len() as u8
                ])?;
                dest.write_all(key)?;
                (value.len() as u16).encode_into(dest)?;
                dest.write_all(value)?;
            },
            Op::Parent => dest.write_all(&[ 0x10 ])?,
            Op::Child => dest.write_all(&[ 0x11 ])?
        };
        Ok(())
    }

    fn encoding_length(&self) -> ed::Result<usize> {
        Ok(match self {
            Op::Push(Node::Hash(_)) => 1 + HASH_LENGTH,
            Op::Push(Node::KVHash(_)) => 1 + HASH_LENGTH,
            Op::Push(Node::KV(key, value)) => 4 + key.len() + value.len(),
            Op::Parent => 1,
            Op::Child => 1
        })
    }
}

impl Decode for Op {
    fn decode<R: Read>(mut input: R) -> ed::Result<Self> {
        let variant: u8 = Decode::decode(&mut input)?;

        Ok(match variant {
            0x01 => {
                let mut hash = [0; HASH_LENGTH];
                input.read_exact(&mut hash)?;
                Op::Push(Node::Hash(hash))
            },
            0x02 => {
                let mut hash = [0; HASH_LENGTH];
                input.read_exact(&mut hash)?;
                Op::Push(Node::KVHash(hash))
            },
            0x03 => {
                let key_len: u8 = Decode::decode(&mut input)?;
                let mut key = Key::with_capacity(key_len as usize);
                key.resize(key_len as usize, 0);
                input.read_exact(key.as_mut_slice())?;

                let value_len: u16 = Decode::decode(&mut input)?;
                let mut value = Value::with_capacity(value_len as usize);
                value.resize(value_len as usize, 0);
                input.read_exact(value.as_mut_slice())?;

                Op::Push(Node::KV(key, value))
            },
            0x10 => Op::Parent,
            0x11 => Op::Child,
            _ => bail!("Proof has unexpected value")
        })
    }
}

impl Terminated for Op {}

impl Op {
    fn encode_into<W: Write>(&self, dest: &mut W) -> Result<()> {
        Encode::encode_into(self, dest)
    }

    fn encoding_length(&self) -> usize {
        Encode::encoding_length(self).unwrap()
    }

    pub fn decode(bytes: &[u8]) -> Result<Self> {
        Decode::decode(bytes)
    }
}

pub fn encode_into<'a, T: Iterator<Item=&'a Op>>(ops: T, output: &mut Vec<u8>) {
    for op in ops {
        op.encode_into(output).unwrap();
    }
}

pub fn encoding_length<'a, T: Iterator<Item=&'a Op>>(ops: T) -> usize {
    ops.map(|op| op.encoding_length()).sum()
}

pub struct Decoder<'a> {
    offset: usize,
    bytes: &'a [u8]
}

impl<'a> Decoder<'a> {
    pub fn new(proof_bytes: &'a [u8]) -> Self {
        Decoder {
            offset: 0,
            bytes: proof_bytes
        }
    }
}

impl<'a> Iterator for Decoder<'a> {
    type Item = Result<Op>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.bytes.len() {
            return None;
        }

        Some((|| {
            let bytes = &self.bytes[self.offset..];
            let op = Op::decode(bytes)?;
            self.offset += op.encoding_length();
            Ok(op)
        })())
    }
}

#[cfg(test)]
mod test {
    use smallvec::smallvec as sv;
    use super::super::{Op, Node};
    use crate::tree::HASH_LENGTH;

    #[test]
    fn encode_push_hash() {
        let op = Op::Push(Node::Hash([123; HASH_LENGTH]));
        assert_eq!(op.encoding_length(), 1 + HASH_LENGTH);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x01, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123]);
    }

    #[test]
    fn encode_push_kvhash() {
        let op = Op::Push(Node::KVHash([123; HASH_LENGTH]));
        assert_eq!(op.encoding_length(), 1 + HASH_LENGTH);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x02, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123]);
    }

    #[test]
    fn encode_push_kv() {
        let op = Op::Push(Node::KV(sv![1, 2, 3], sv![4, 5, 6]));
        assert_eq!(op.encoding_length(), 10);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x03, 3, 1, 2, 3, 0, 3, 4, 5, 6]);
    }

    #[test]
    fn encode_parent() {
        let op = Op::Parent;
        assert_eq!(op.encoding_length(), 1);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x10]);
    }

    #[test]
    fn encode_child() {
        let op = Op::Child;
        assert_eq!(op.encoding_length(), 1);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x11]);
    }

    #[test]
    #[should_panic]
    fn encode_push_kv_long_key() {
        let op = Op::Push(Node::KV(sv![123; 300], sv![4, 5, 6]));
        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
    }

    #[test]
    fn decode_push_hash() {
        let bytes = [0x01, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Push(Node::Hash([123; HASH_LENGTH])));
    }

    #[test]
    fn decode_push_kvhash() {
        let bytes = [0x02, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Push(Node::KVHash([123; HASH_LENGTH])));
    }

    #[test]
    fn decode_push_kv() {
        let bytes = [0x03, 3, 1, 2, 3, 0, 3, 4, 5, 6];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Push(Node::KV(sv![1, 2, 3], sv![4, 5, 6])));
    }

    #[test]
    fn decode_parent() {
        let bytes = [0x10];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Parent);
    }

    #[test]
    fn decode_child() {
        let bytes = [0x11];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Child);
    }

    #[test]
    fn decode_unknown() {
        let bytes = [0x88];
        assert!(Op::decode(&bytes[..]).is_err());
    }
}
