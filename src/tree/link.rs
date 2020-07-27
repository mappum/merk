use std::cmp::max;
use smallvec::SmallVec;
use super::hash::Hash;
use super::{Tree, Key, Value};

// TODO: optimize memory footprint

/// Represents a reference to a child tree node. Links may or may not contain
/// the child's `Tree` instance (storing its key if not).
pub enum Link {
    /// Represents a child tree node which has been pruned from memory, only
    /// retaining its key. The child node can always be fetched from the backing
    /// store by this key when necessary.
    Pruned {
        hash: Hash,
        child_heights: (u8, u8),
        key: Key
    },

    /// Represents a tree node which has been modified since the `Tree`'s last
    /// commit. The child's hash is not stored since it has not yet been
    /// recomputed. The child's `Tree` instance is stored in the link.
    Modified {
        pending_writes: usize,
        child_heights: (u8, u8),
        tree: Tree
    },

    /// Represents a tree node which has not been modified, has an up-to-date
    /// hash, and which is being retained in memory.
    Stored {
        hash: Hash,
        child_heights: (u8, u8),
        tree: Tree
    }
}

impl Link {
    /// Creates a `Link::Modified` from the given `Tree`.
    #[inline]
    pub fn from_modified_tree(tree: Tree) -> Self {
        let pending_writes = 1
            + tree.child_pending_writes(true)
            + tree.child_pending_writes(false);

        Link::Modified {
            pending_writes,
            child_heights: tree.child_heights(),
            tree
        }
    }

    /// Creates a `Link::Modified` from the given tree, if any. If `None`,
    /// returns `None`.
    pub fn maybe_from_modified_tree(maybe_tree: Option<Tree>) -> Option<Self> {
        maybe_tree.map(Link::from_modified_tree)
    }

    /// Returns `true` if the link is of the `Link::Pruned` variant.
    #[inline]
    pub fn is_pruned(&self) -> bool {
        match self {
            Link::Pruned { .. } => true,
            _ => false
        }
    }

    /// Returns `true` if the link is of the `Link::Modified` variant.
    #[inline]
    pub fn is_modified(&self) -> bool {
        match self {
            Link::Modified { .. } => true,
            _ => false
        }
    }

    /// Returns `true` if the link is of the `Link::Stored` variant.
    #[inline]
    pub fn is_stored(&self) -> bool {
        match self {
            Link::Stored { .. } => true,
            _ => false
        }
    }

    /// Returns the key of the tree referenced by this link, as a slice.
    pub fn key(&self) -> &[u8] {
        match self {
            Link::Pruned { key, .. } => key.as_slice(),
            Link::Modified { tree, .. } => tree.key(),
            Link::Stored { tree, .. } => tree.key()
        }
    }

    /// Returns the `Tree` instance of the tree referenced by the link. If the
    /// link is of variant `Link::Pruned`, the returned value will be `None`.
    pub fn tree(&self) -> Option<&Tree> {
        match self {
            // TODO: panic for Pruned, don't return Option?
            Link::Pruned { .. } => None,
            Link::Modified { tree, .. } => Some(tree),
            Link::Stored { tree, .. } => Some(tree)
        }
    }

    /// Returns the hash of the tree referenced by the link. Panics if link is
    /// of variant `Link::Modified` since we have not yet recomputed the tree's
    /// hash.
    pub fn hash(&self) -> &Hash {
        match self {
            Link::Modified { .. } => panic!("Cannot get hash from modified link"),
            Link::Pruned { hash, .. } => hash,
            Link::Stored { hash, .. } => hash
        }
    }

    /// Returns the height of the children of the tree referenced by the link,
    /// if any (note: not the height of the referenced tree itself). Return
    /// value is `(left_child_height, right_child_height)`.
    pub fn height(&self) -> u8 {
        let (left_height, right_height) = match self {
            Link::Pruned { child_heights, .. } => *child_heights,
            Link::Modified { child_heights, .. } => *child_heights,
            Link::Stored { child_heights, .. } => *child_heights
        };
        1 + max(left_height, right_height)
    }
    
    /// Returns the balance factor of the tree referenced by the link.
    #[inline]
    pub fn balance_factor(&self) -> i8 {
        let (left_height, right_height) = match self {
            Link::Pruned { child_heights, .. } => *child_heights,
            Link::Modified { child_heights, .. } => *child_heights,
            Link::Stored { child_heights, .. } => *child_heights
        };
        right_height as i8 - left_height as i8
    }

    /// Consumes the link and converts to variant `Link::Pruned`. Panics if the
    /// link is of variant `Link::Modified`.
    pub fn into_pruned(self) -> Self {
        match self {
            Link::Pruned { .. } => self,
            Link::Modified { .. } => panic!("Cannot prune Modified tree"),
            Link::Stored { hash, child_heights, tree } => Link::Pruned {
                hash,
                child_heights,
                key: tree.take_key()
            }
        }
    }
}

#[cfg(test)]
mod test {
    use smallvec::smallvec;
    use super::*;
    use super::super::Tree;
    use super::super::hash::NULL_HASH;
    
    #[test]
    fn from_modified_tree() {
        let tree = Tree::new(smallvec![0], vec![1]);
        let link = Link::from_modified_tree(tree);
        assert!(link.is_modified());
        assert_eq!(link.height(), 1);
        assert_eq!(link.tree().expect("expected tree").key(), &[0]);
        if let Link::Modified { pending_writes, .. } = link {
            assert_eq!(pending_writes, 1);
        } else {
            panic!("Expected Link::Modified");
        }
    }

    #[test]
    fn maybe_from_modified_tree() {
        let link = Link::maybe_from_modified_tree(None);
        assert!(link.is_none());

        let tree = Tree::new(smallvec![0], vec![1]);
        let link = Link::maybe_from_modified_tree(Some(tree));
        assert!(link.expect("expected link").is_modified());
    }

    #[test]
    fn types() {
        let hash = NULL_HASH;
        let child_heights = (0, 0);
        let pending_writes = 1;
        let key = smallvec![0];
        let tree = || Tree::new(smallvec![0], vec![1]);

        let pruned = Link::Pruned { hash, child_heights, key };
        let modified = Link::Modified { pending_writes, child_heights, tree: tree() };
        let stored = Link::Stored { hash, child_heights, tree: tree() };

        assert!(pruned.is_pruned());
        assert!(!pruned.is_modified());
        assert!(!pruned.is_stored());
        assert!(pruned.tree().is_none());
        assert_eq!(pruned.hash(), &[0; 20]);
        assert_eq!(pruned.height(), 1);
        assert!(pruned.into_pruned().is_pruned());

        assert!(!modified.is_pruned());
        assert!(modified.is_modified());
        assert!(!modified.is_stored());
        assert!(modified.tree().is_some());
        assert_eq!(modified.height(), 1);

        assert!(!stored.is_pruned());
        assert!(!stored.is_modified());
        assert!(stored.is_stored());
        assert!(stored.tree().is_some());
        assert_eq!(stored.hash(), &[0; 20]);
        assert_eq!(stored.height(), 1);
        assert!(stored.into_pruned().is_pruned());
    }

    #[test]
    #[should_panic]
    fn modified_hash() {
        Link::Modified {
            pending_writes: 1,
            child_heights: (1, 1),
            tree: Tree::new(smallvec![0], vec![1])
        }.hash();
    }

    #[test]
    #[should_panic]
    fn modified_into_pruned() {
        Link::Modified {
            pending_writes: 1,
            child_heights: (1, 1),
            tree: Tree::new(smallvec![0], vec![1])
        }.into_pruned();
    }
}
