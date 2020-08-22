use super::{Key, Value};
use super::hash::{Hash, kv_hash};

// TODO: maybe use something similar to Vec but without capacity field,
//       (should save 16 bytes per entry). also, maybe a shorter length
//       field to save even more. also might be possible to combine key
//       field and value field.

/// Contains a key/value pair, and the hash of the key/value pair.
pub struct KV {
    key: Key,
    value: Value,
    hash: Hash
}

impl KV {
    /// Creates a new `KV` with the given key and value and computes its hash.
    #[inline]
    pub fn new(key: Key, value: Value) -> Self {
        // TODO: length checks?
        let hash = kv_hash(key.as_slice(), value.as_slice());
        KV { key, value, hash }
    }

    /// Creates a new `KV` with the given key, value, and hash. The hash is not
    /// checked to be correct for the given key/value.
    #[inline]
    pub fn from_fields(key: Key, value: Value, hash: Hash) -> Self {
        KV { key, value, hash }
    }

    /// Replaces the `KV`'s value with the given value, updates the hash, and
    /// returns the modified `KV`.
    #[inline]
    pub fn with_value(mut self, value: Value) -> Self {
        // TODO: length check?
        self.value = value;
        self.hash = kv_hash(self.key(), self.value());
        self
    }

    /// Returns the key as a slice.
    #[inline]
    pub fn key(&self) -> &[u8] {
        self.key.as_slice()
    }
    
    /// Returns the value as a slice.
    #[inline]
    pub fn value(&self) -> &[u8] {
        self.value.as_slice()
    }

    /// Returns the hash.
    #[inline]
    pub fn hash(&self) -> &Hash {
        &self.hash
    }

    /// Consumes the `KV` and returns its key without allocating or cloning.
    #[inline]
    pub fn take_key(self) -> Key {
        self.key
    }
}

#[cfg(test)]
mod test {
    use smallvec::smallvec as vec;
    use super::*;

    #[test]
    fn new_kv() {
        let kv = KV::new(vec![1, 2, 3], vec![4, 5, 6]);

        assert_eq!(kv.key(), &[1, 2, 3]);
        assert_eq!(kv.value(), &[4, 5, 6]);
        assert_ne!(kv.hash(), &super::super::hash::NULL_HASH);
    }

    #[test]
    fn with_value() {
        let kv = KV::new(vec![1, 2, 3], vec![4, 5, 6])
            .with_value(vec![7, 8, 9]);

        assert_eq!(kv.key(), &[1, 2, 3]);
        assert_eq!(kv.value(), &[7, 8, 9]);
        assert_ne!(kv.hash(), &super::super::hash::NULL_HASH);
    }
}
