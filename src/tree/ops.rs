use std::collections::LinkedList;
use std::fmt;
use failure::bail;
use crate::error::Result;
use super::{Tree, Link, Walker, Fetch, Key, Value};
use Op::*;

/// An operation to be applied to a key in the store.
pub enum Op {
    Put(Value),
    Delete
}

impl fmt::Debug for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}", match self {
            Put(value) => format!("Put({:?})", value),
            Delete => "Delete".to_string()
        })
    }
}

/// A single `(key, operation)` pair.
pub type BatchEntry = (Key, Op);

/// A mapping of keys and operations. Keys should be sorted and unique.
pub type Batch = [BatchEntry];

/// A source of data which panics when called. Useful when creating a store
/// which always keeps the state in memory.
#[derive(Clone)]
pub struct PanicSource {}
impl Fetch for PanicSource {
    fn fetch(&self, _link: &Link) -> Result<Tree> {
        unreachable!("'fetch' should not have been called")
    }
}

impl<S> Walker<S>
    where S: Fetch + Sized + Send + Clone
{
    /// Applies a batch of operations, possibly creating a new tree if
    /// `maybe_tree` is `None`. This is similar to `Walker<S>::apply`, but does
    /// not require a non-empty tree.
    /// 
    /// Keys in batch must be sorted and unique.
    pub fn apply_to(
        maybe_tree: Option<Self>,
        batch: &Batch
    ) -> Result<(Option<Tree>, LinkedList<Key>)> {
        let (maybe_walker, deleted_keys) = if batch.is_empty() {
            (maybe_tree, LinkedList::default())
        } else {
            match maybe_tree {
                None => return Ok((
                    Self::build(batch)?,
                    LinkedList::default()
                )),
                Some(tree) => tree.apply(batch)?
            }
        };

        let maybe_tree = maybe_walker
            .map(|walker| walker.into_inner());
        Ok((maybe_tree, deleted_keys))
    }

    /// Builds a `Tree` from a batch of inserts. Fails if the batch contains a
    /// `Delete` operation.
    /// 
    /// Keys in batch must be sorted and unique.
    fn build(batch: &Batch) -> Result<Option<Tree>> {
        if batch.is_empty() {
            return Ok(None);
        }

        let mid_index = batch.len() / 2;
        let (mid_key, mid_op) = &batch[mid_index];
        let mid_value = match mid_op {
            Delete => bail!("Tried to delete non-existent key {:?}", mid_key),
            Put(value) => value
        };

        // TODO: take from batch so we don't have to clone
        let mid_tree = Tree::new(mid_key.clone(), mid_value.clone());
        let mid_walker = Walker::new(mid_tree, PanicSource {});
        Ok(mid_walker
            .recurse(batch, mid_index, true)?
            .0 // use walker, ignore deleted_keys since it should be empty
            .map(|w| w.into_inner()))
    }

    /// Applies a batch of operations to an existing tree. This is similar to
    /// `Walker<S>::apply`_to, but requires a populated tree.
    ///
    /// Keys in batch must be sorted and unique.
    fn apply(
        self,
        batch: &Batch
    ) -> Result<(Option<Self>, LinkedList<Key>)> {
        // binary search to see if this node's key is in the batch, and to split
        // into left and right batches
        let search = batch.binary_search_by(
            |(key, _op)| key.as_slice().cmp(self.tree().key())
        );
        let tree = if let Ok(index) = search {
            // a key matches this node's key, apply op to this node
            match &batch[index].1 {
                // TODO: take vec from batch so we don't need to clone
                Put(value) => self.with_value(value.clone()),
                Delete => {
                    // TODO: we shouldn't have to do this as 2 different calls to apply
                    let source = self.clone_source();
                    let wrap = |maybe_tree: Option<Tree>| {
                        maybe_tree.map(|tree| Self::new(tree, source.clone()))
                    };
                    let key = self.tree().key().into();
                    let maybe_tree = self.remove()?;

                    let (maybe_tree, mut deleted_keys) =
                        Self::apply_to(maybe_tree, &batch[..index])?;
                    let maybe_walker = wrap(maybe_tree);

                    let (maybe_tree, mut deleted_keys_right) =
                        Self::apply_to(maybe_walker, &batch[index + 1..])?;
                    let maybe_walker = wrap(maybe_tree);

                    deleted_keys.append(&mut deleted_keys_right);
                    deleted_keys.push_back(key);

                    return Ok((maybe_walker, deleted_keys));
                }
            }
        } else {
            self
        };

        let (mid, exclusive) = match search {
            Ok(index) => (index, true),
            Err(index) => (index, false)
        };

        tree.recurse(batch, mid, exclusive)
    }

    /// Recursively applies operations to the tree's children (if there are any
    /// operations for them).
    ///
    /// This recursion executes serially in the same thread, but in the future
    /// will be dispatched to workers in other threads.
    fn recurse(
        self,
        batch: &Batch,
        mid: usize,
        exclusive: bool
    ) -> Result<(Option<Self>, LinkedList<Key>)> {
        let left_batch = &batch[..mid];
        let right_batch = if exclusive {
            &batch[mid + 1..]
        } else {
            &batch[mid..]
        };
        
        let mut deleted_keys = LinkedList::default();

        let tree = if !left_batch.is_empty() {
            self.walk(true, |maybe_left| {
                let (maybe_left, mut deleted_keys_left) =
                    Self::apply_to(maybe_left, left_batch)?;
                deleted_keys.append(&mut deleted_keys_left);
                Ok(maybe_left)
            })?
        } else {
            self
        };

        let tree = if !right_batch.is_empty() {
            tree.walk(false, |maybe_right| {
                let (maybe_right, mut deleted_keys_right) =
                    Self::apply_to(maybe_right, right_batch)?;
                deleted_keys.append(&mut deleted_keys_right);
                Ok(maybe_right)
            })?
        } else {
            tree
        };

        let tree = tree.maybe_balance()?;

        Ok((Some(tree), deleted_keys))
    }

    /// Gets the wrapped tree's balance factor.
    #[inline]
    fn balance_factor(&self) -> i8 {
        self.tree().balance_factor()
    }

    /// Checks if the tree is unbalanced and if so, applies AVL tree rotation(s)
    /// to rebalance the tree and its subtrees. Returns the root node of the
    /// balanced tree after applying the rotations.
    fn maybe_balance(self) -> Result<Self> {
        let balance_factor = self.balance_factor();
        if balance_factor.abs() <= 1 {
            return Ok(self);
        }

        let left = balance_factor < 0;

        // maybe do a double rotation
        let tree = if left == (self.tree().link(left).unwrap().balance_factor() > 0) {
            self.walk_expect(left, |child| Ok(Some(child.rotate(!left)?)))?
        } else {
            self
        };
        
        tree.rotate(left)
    }

    /// Applies an AVL tree rotation, a constant-time operation which only needs
    /// to swap pointers in order to rebalance a tree.
    fn rotate(self, left: bool) -> Result<Self> {
        unsafe {
            let (tree, child) = self.detach_expect(left)?;
            let (child, maybe_grandchild) = child.detach(!left)?;

            // attach grandchild to self
            let tree = tree
                .attach(left, maybe_grandchild)
                .maybe_balance()?;

            // attach self to child, return child
            child
                .attach(!left, Some(tree))
                .maybe_balance()
        }
    }

    /// Removes the root node from the tree. Rearranges and rebalances
    /// descendants (if any) in order to maintain a valid tree.
    pub fn remove(self) -> Result<Option<Self>> {
        let tree = self.tree();
        let has_left = tree.link(true).is_some();
        let has_right = tree.link(false).is_some();
        let left = tree.child_height(true) > tree.child_height(false);

        let maybe_tree = unsafe {
            if has_left && has_right {
                // two children, promote edge of taller child
                let (tree, tall_child) = self.detach_expect(left)?;
                let (_, short_child) = tree.detach_expect(!left)?;
                Some(tall_child.promote_edge(!left, short_child)?)
            } else if has_left || has_right {
                // single child, promote it
                Some(self.detach_expect(left)?.1)
            } else {
                // no child
                None
            }
        };

        Ok(maybe_tree)
    }

    /// Traverses to find the tree's edge on the given side, removes it, and
    /// reattaches it at the top in order to fill in a gap when removing a root
    /// node from a tree with both left and right children. Attaches `attach` on
    /// the opposite side. Returns the promoted node.
    fn promote_edge(self, left: bool, attach: Self) -> Result<Self> {
        let (edge, maybe_child) = self.remove_edge(left)?;
        edge
            .attach(!left, maybe_child)
            .attach(left, Some(attach))
            .maybe_balance()
    }

    /// Traverses to the tree's edge on the given side and detaches it
    /// (reattaching its child, if any, to its former parent). Return value is
    /// `(edge, maybe_updated_tree)`.
    fn remove_edge(self, left: bool) -> Result<(Self, Option<Self>)> {
        if self.tree().link(left).is_some() {
            // this node is not the edge, recurse
            let (tree, child) = unsafe { self.detach_expect(left)? };
            let (edge, maybe_child) = child.remove_edge(left)?;
            let tree = tree
                .attach(left, maybe_child)
                .maybe_balance()?;
            Ok((edge, Some(tree)))
        } else {
            // this node is the edge, detach its child if present
            unsafe { self.detach(!left) }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::tree::*;
    use crate::test_utils::{
        make_tree_seq,
        del_entry,
        apply_memonly,
        assert_tree_invariants,
        seq_key
    };

    #[test]
    fn simple_insert() {
        let batch = [
            (
                b"foo2".to_vec(),
                Op::Put(b"bar2".to_vec())
            )
        ];
        let tree = Tree::new(b"foo".to_vec(), b"bar".to_vec());
        let (maybe_walker, deleted_keys) = Walker::new(tree, PanicSource {})
            .apply(&batch)
            .expect("apply errored");
        let walker = maybe_walker.expect("should be Some");
        assert_eq!(walker.tree().key(), b"foo");
        assert_eq!(walker.into_inner().child(false).unwrap().key(), b"foo2");
        assert!(deleted_keys.is_empty());
    }

    #[test]
    fn simple_update() {
        let batch = [
            (
                b"foo".to_vec(),
                Op::Put(b"bar2".to_vec())
            )
        ];
        let tree = Tree::new(b"foo".to_vec(), b"bar".to_vec());
        let (maybe_walker, deleted_keys) = Walker::new(tree, PanicSource {})
            .apply(&batch)
            .expect("apply errored");
        let walker = maybe_walker.expect("should be Some");
        assert_eq!(walker.tree().key(), b"foo");
        assert_eq!(walker.tree().value(), b"bar2");
        assert!(walker.tree().link(true).is_none());
        assert!(walker.tree().link(false).is_none());
        assert!(deleted_keys.is_empty());
    }

    #[test]
    fn simple_delete() {
        let batch = [
            (b"foo2".to_vec(), Op::Delete)
        ];
        let tree = Tree::from_fields(
            b"foo".to_vec(), b"bar".to_vec(),
            [123; 20],
            None,
            Some(Link::Stored {
                hash: [123; 20],
                child_heights: (0, 0),
                tree: Tree::new(b"foo2".to_vec(), b"bar2".to_vec())
            })
        );
        let (maybe_walker, deleted_keys) = Walker::new(tree, PanicSource {})
            .apply(&batch)
            .expect("apply errored");
        let walker = maybe_walker.expect("should be Some");
        assert_eq!(walker.tree().key(), b"foo");
        assert_eq!(walker.tree().value(), b"bar");
        assert!(walker.tree().link(true).is_none());
        assert!(walker.tree().link(false).is_none());
        assert_eq!(deleted_keys.len(), 1);
        assert_eq!(*deleted_keys.front().unwrap(), b"foo2");
    }

    #[test]
    #[should_panic]
    fn delete_non_existent() {
        let batch = [
            (b"foo2".to_vec(), Op::Delete)
        ];
        let tree = Tree::new(b"foo".to_vec(), b"bar".to_vec());
        Walker::new(tree, PanicSource {})
            .apply(&batch)
            .unwrap();
    }

    #[test]
    fn delete_only_node() {
        let batch = [
            (b"foo".to_vec(), Op::Delete)
        ];
        let tree = Tree::new(b"foo".to_vec(), b"bar".to_vec());
        let (maybe_walker, deleted_keys) = Walker::new(tree, PanicSource {})
            .apply(&batch)
            .expect("apply errored");
        assert!(maybe_walker.is_none());
        assert_eq!(deleted_keys.len(), 1);
        assert_eq!(deleted_keys.front().unwrap(), b"foo");
    }

    #[test]
    fn delete_deep() {
        let tree = make_tree_seq(50);
        let batch = [ del_entry(5) ]; 
        let (maybe_walker, deleted_keys) = Walker::new(tree, PanicSource {})
            .apply(&batch)
            .expect("apply errored");
        maybe_walker.expect("should be Some");
        assert_eq!(deleted_keys.len(), 1);
        assert_eq!(*deleted_keys.front().unwrap(), seq_key(5));
    }

    #[test]
    fn delete_recursive() {
        let tree = make_tree_seq(50);
        let batch = [ del_entry(29), del_entry(34) ]; 
        let (maybe_walker, mut deleted_keys) = Walker::new(tree, PanicSource {})
            .apply(&batch)
            .expect("apply errored");
        maybe_walker.expect("should be Some");
        assert_eq!(deleted_keys.len(), 2);
        assert_eq!(deleted_keys.pop_front().unwrap(), seq_key(29));
        assert_eq!(deleted_keys.pop_front().unwrap(), seq_key(34));
    }

    #[test]
    fn delete_recursive_2() {
        let tree = make_tree_seq(10);
        let batch = [ del_entry(7), del_entry(9) ]; 
        let (maybe_walker, deleted_keys) = Walker::new(tree, PanicSource {})
            .apply(&batch)
            .expect("apply errored");
        maybe_walker.expect("should be Some");
        let mut deleted_keys: Vec<&Vec<u8>> = deleted_keys.iter().collect();
        deleted_keys.sort_by(|a, b| a.cmp(&b));
        assert_eq!(deleted_keys, vec![ &seq_key(7), &seq_key(9) ]);
    }

    #[test]
    fn apply_empty_none() {
        let (maybe_tree, deleted_keys) = Walker::<PanicSource>::apply_to(None, &vec![])
            .expect("apply_to failed");
        assert!(maybe_tree.is_none());
        assert!(deleted_keys.is_empty());
    }

    #[test]
    fn insert_empty_single() {
        let batch = vec![ (vec![0], Op::Put(vec![1])) ];
        let (maybe_tree, deleted_keys) = Walker::<PanicSource>::apply_to(None, &batch)
            .expect("apply_to failed");
        let tree = maybe_tree.expect("expected tree");
        assert_eq!(tree.key(), &[0]);
        assert_eq!(tree.value(), &[1]);
        assert_tree_invariants(&tree);
        assert!(deleted_keys.is_empty());
    }

    #[test]
    fn insert_root_single() {
        let tree = Tree::new(vec![5], vec![123]);
        let batch = vec![ (vec![6], Op::Put(vec![123])) ];
        let tree = apply_memonly(tree, &batch);
        assert_eq!(tree.key(), &[5]);
        assert!(tree.child(true).is_none());
        assert_eq!(tree.child(false).expect("expected child").key(), &[6]);
    }

    #[test]
    fn insert_root_double() {
        let tree = Tree::new(vec![5], vec![123]);
        let batch = vec![
            (vec![4], Op::Put(vec![123])),
            (vec![6], Op::Put(vec![123]))
        ];
        let tree = apply_memonly(tree, &batch);
        assert_eq!(tree.key(), &[5]);
        assert_eq!(tree.child(true).expect("expected child").key(), &[4]);
        assert_eq!(tree.child(false).expect("expected child").key(), &[6]);
    }

    #[test]
    fn insert_rebalance() {
        let tree = Tree::new(vec![5], vec![123]);

        let batch = vec![ (vec![6], Op::Put(vec![123])) ];
        let tree = apply_memonly(tree, &batch);

        let batch = vec![ (vec![7], Op::Put(vec![123])) ];
        let tree = apply_memonly(tree, &batch);

        assert_eq!(tree.key(), &[6]);
        assert_eq!(tree.child(true).expect("expected child").key(), &[5]);
        assert_eq!(tree.child(false).expect("expected child").key(), &[7]);
    }

    #[test]
    fn insert_100_sequential() {
        let mut tree = Tree::new(vec![0], vec![123]);

        for i in 0..100 {
            let batch = vec![ (vec![i + 1], Op::Put(vec![123])) ];
            tree = apply_memonly(tree, &batch);
        }

        assert_eq!(tree.key(), &[63]);
        assert_eq!(tree.child(true).expect("expected child").key(), &[31]);
        assert_eq!(tree.child(false).expect("expected child").key(), &[79]);
    }
}
