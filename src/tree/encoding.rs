use std::convert::TryInto;

use super::{Tree, Link, Hash, Key, Value};
use crate::error::Result;

// TODO: Encode, Decode traits

impl Link {
    // TODO: encode_recursive_into? doesn't convert into pruned

    /// Pushes a bianry encoding of the `Link` into the given byte vector.
    pub fn encode_into(&self, output: &mut Vec<u8>) {
        let (hash, key, (left_height, right_height)) = match self {
            Link::Pruned { hash, key, child_heights } => (hash, key.as_slice(), child_heights),
            Link::Stored { hash, tree, child_heights } => (hash, tree.key(), child_heights),
            Link::Modified { .. } => panic!("No encoding for Link::Modified")
        };

        output.push(key.len().try_into().unwrap());
        output.extend_from_slice(key);

        output.extend_from_slice(hash);

        output.push(*left_height);
        output.push(*right_height);
    }

    /// Returns the size of the `Link`'s binary encoding, in bytes.
    pub fn encoding_length(&self) -> usize {
        match self {
            Link::Pruned { key, .. } => { 1 + key.len() + 20 + 2 },
            Link::Modified { .. } => panic!("No encoding for Link::Modified"),
            Link::Stored { tree, .. } => { 1 + tree.key().len() + 20 + 2 }
        }
    }

    /// Decodes a `Link` from its binary encoding.
    pub fn decode(bytes: &[u8]) -> Result<Link> {
        let mut offset = 0;

        let length = bytes[offset] as usize;
        offset += 1;

        let key = bytes[offset..offset + length].into();
        offset += length as usize;

        let mut hash: Hash = Default::default();
        hash.copy_from_slice(&bytes[offset..offset + 20]);
        offset += 20;

        let child_heights = (bytes[offset], bytes[offset + 1]);
        // offset += 2;

        Ok(Link::Pruned { key, hash, child_heights })
    }
}

impl Tree {
    /// Pushes a bianry encoding of the `Tree` into the given byte vector.
    pub fn encode_into(&self, output: &mut Vec<u8>) {
        let value_len = self.value().len();
        // TODO: use byteorder package
        output.push((value_len & 0xff).try_into().unwrap());
        output.push((value_len >> 8).try_into().unwrap());
        output.extend_from_slice(self.value());

        output.extend_from_slice(self.inner.kv.hash());

        match self.link(true) {
            None => output.push(0),
            Some(link) => link.encode_into(output)
        }

        match self.link(false) {
            None => output.push(0),
            Some(link) => link.encode_into(output)
        }
    }

    /// Returns the size of the `Tree`'s binary encoding, in bytes.
    pub fn encoding_length(&self) -> usize {
        2 + // value length
        self.inner.kv.value().len() + // value bytes
        20 + // kv_hash length
        self.link(true).map_or(1, |link| link.encoding_length()) +
        self.link(false).map_or(1, |link| link.encoding_length())
    }

    /// Decodes a `Tree` from its binary encoding.
    pub fn decode(key: &[u8], bytes: &[u8]) -> Result<Tree> {
        let mut offset = 0;

        let value_len =
            bytes[offset] as usize
            + ((bytes[offset + 1] as usize) << 8);
        offset += 2;

        let value = bytes[offset..offset + value_len].into();
        offset += value_len;

        let mut kv_hash: Hash = Default::default();
        kv_hash.copy_from_slice(&bytes[offset..(offset + 20)]);
        offset += 20;

        let link_length = bytes[offset];
        let left = if link_length > 0 {
            let link = Link::decode(&bytes[offset..])?;
            offset += link.encoding_length();
            Some(link)
        } else {
            offset += 1;
            None
        };

        let link_length = bytes[offset];
        let right = if link_length > 0 {
            let link = Link::decode(&bytes[offset..])?;
            // offset += link.encoding_length();
            Some(link)
        } else {
            // offset += 1;
            None
        };

        Ok(Tree::from_fields(
            key.into(),
            value,
            kv_hash,
            left,
            right
        ))
    }
}

#[cfg(test)]
mod test {
    use smallvec::smallvec as sv;
    use super::super::{Tree, Link};

    #[test]
    fn encode_leaf_tree() {
        let tree = Tree::new(sv![0], sv![1]);
        assert_eq!(tree.encoding_length(), 25);

        let mut bytes = vec![];
        tree.encode_into(&mut bytes);
        assert_eq!(bytes, vec![1, 0, 1, 195, 201, 244, 70, 50, 255, 177, 215, 40, 246, 8, 69, 174, 17, 72, 99, 29, 112, 226, 212, 0, 0]);
    }

    #[test]
    fn encode_link() {
        let link = Link::Pruned {
            key: sv![1, 2, 3],
            child_heights: (123, 124),
            hash: [55; 20]
        };
        assert_eq!(link.encoding_length(), 26);

        let mut bytes = vec![];
        link.encode_into(&mut bytes);
        assert_eq!(bytes, vec![3, 1, 2, 3, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 123, 124]);
    }

    #[test]
    #[should_panic]
    fn encode_link_long_key() {
        let link = Link::Pruned {
            key: sv![123; 300],
            child_heights: (123, 124),
            hash: [55; 20]
        };
        let mut bytes = vec![];
        link.encode_into(&mut bytes);
    }

    #[test]
    #[should_panic]
    fn encode_modified_tree() {
        let tree = Tree::from_fields(
            sv![0], sv![1],
            [55; 20],
            Some(Link::Modified {
                pending_writes: 1,
                child_heights: (123, 124),
                tree: Tree::new(sv![2], sv![3])
            }),
            None
        );
        let mut bytes = vec![];
        tree.encode_into(&mut bytes);
    }

    #[test]
    fn encode_stored_tree() {
        let tree = Tree::from_fields(
            sv![0], sv![1],
            [55; 20],
            Some(Link::Stored {
                hash: [66; 20],
                child_heights: (123, 124),
                tree: Tree::new(sv![2], sv![3])
            }),
            None
        );
        let mut bytes = vec![];
        tree.encode_into(&mut bytes);
        assert_eq!(bytes, vec![1, 0, 1, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 1, 2, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 123, 124, 0].as_slice());
    }

    #[test]
    fn encode_pruned_tree() {
        let tree = Tree::from_fields(
            sv![0], sv![1],
            [55; 20],
            Some(Link::Pruned {
                hash: [66; 20],
                child_heights: (123, 124),
                key: sv![2]
            }),
            None
        );
        assert_eq!(tree.encoding_length(), 48);
        
        let mut bytes = vec![];
        tree.encode_into(&mut bytes);
        assert_eq!(bytes, vec![1, 0, 1, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 1, 2, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 123, 124, 0].as_slice());
    }

    #[test]
    fn decode_leaf_tree() {
        let bytes = vec![1, 0, 1, 195, 201, 244, 70, 50, 255, 177, 215, 40, 246, 8, 69, 174, 17, 72, 99, 29, 112, 226, 212, 0, 0];
        let tree = Tree::decode(&[0], bytes.as_slice()).expect("decode failed");
        assert_eq!(tree.key(), &[0]);
        assert_eq!(tree.value(), &[1]);
    }

    #[test]
    fn decode_pruned_tree() {
        let bytes = vec![1, 0, 1, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 1, 2, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 123, 124, 0];
        let tree = Tree::decode(&[0], bytes.as_slice()).expect("decode failed");
        assert_eq!(tree.key(), &[0]);
        assert_eq!(tree.value(), &[1]);
        if let Some(Link::Pruned { key, child_heights, hash }) = tree.link(true) {
            assert_eq!(&key[..], &[2][..]);
            assert_eq!(child_heights, &(123 as u8, 124 as u8));
            assert_eq!(hash, &[66 as u8; 20]);
        } else {
            panic!("Expected Link::Pruned");
        }
    }
}
