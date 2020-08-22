mod chunk;
mod encoding;
mod query;
mod verify;

use crate::tree::{Link, RefWalker, Fetch, Hash, Key, Value};

pub use encoding::{encode_into, Decoder};
pub use verify::verify;

/// A proof operator, executed to verify the data in a Merkle proof.
#[derive(Debug, PartialEq)]
pub enum Op {
    /// Pushes a node on the stack.
    Push(Node),

    /// Pops the top stack item as `parent`. Pops the next top stack item as
    /// `child`. Attaches `child` as the left child of `parent`. Pushes the
    /// updated `parent` back on the stack.
    Parent,

    /// Pops the top stack item as `child`. Pops the next top stack item as
    /// `parent`. Attaches `child` as the right child of `parent`. Pushes the
    /// updated `parent` back on the stack.
    Child
}

/// A selected piece of data about a single tree node, to be contained in a
/// `Push` operator in a proof.
#[derive(Clone, Debug, PartialEq)]
pub enum Node {
    /// Represents the hash of a tree node.
    Hash(Hash),

    /// Represents the hash of the key/value pair of a tree node.
    KVHash(Hash),

    /// Represents the key and value of a tree node.
    KV(Key, Value)
}

