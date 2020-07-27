mod fetch;
mod ref_walker;

pub use fetch::Fetch;
pub use ref_walker::RefWalker;
use crate::error::Result;
use super::{Tree, Link, Key, Value};
use crate::owner::Owner;

/// Allows traversal of a `Tree`, fetching from the given source when traversing
/// to a pruned node, detaching children as they are traversed.
pub struct Walker<S>
    where S: Fetch + Sized + Clone + Send
{
    tree: Owner<Tree>,
    source: S
}

impl<S> Walker<S>
    where S: Fetch + Sized + Clone + Send
{
    /// Creates a `Walker` with the given tree and source.
    pub fn new(tree: Tree, source: S) -> Self {
        Walker { tree: Owner::new(tree), source }
    }

    /// Similar to `Tree#detach`, but yields a `Walker` which fetches from the
    /// same source as `self`. Returned tuple is `(updated_self, maybe_child_walker)`.
    pub unsafe fn detach(mut self, left: bool) -> Result<(Self, Option<Self>)> {
        let link = match self.tree.link(left) {
            None => return Ok((self, None)),
            Some(link) => link
        };

        let child = if link.tree().is_some() {
            match self.tree.own_return(|t| t.detach(left)) {
                Some(child) => child,
                _ => unreachable!("Expected Some")
            }
        } else {
            let link = self.tree.slot_mut(left).take();
            match link {
                Some(Link::Pruned { .. }) => (),
                _ => unreachable!("Expected Some(Link::Pruned)")
            }
            self.source.fetch(&link.unwrap())?
        };

        let child = self.wrap(child);
        Ok((self, Some(child)))
    }

    /// Similar to `Tree#detach_expect`, but yields a `Walker` which fetches
    /// from the same source as `self`. Returned tuple is `(updated_self, child_walker)`.
    pub unsafe fn detach_expect(self, left: bool) -> Result<(Self, Self)> {
        let (walker, maybe_child) = self.detach(left)?;
        if let Some(child) = maybe_child {
            Ok((walker, child))
        } else {
            panic!(
                "Expected {} child, got None",
                if left { "left" } else { "right" }
            );
        }
    }

    /// Similar to `Tree#walk`, but yields a `Walker` which fetches from the
    /// same source as `self`.
    pub fn walk<F, T>(self, left: bool, f: F) -> Result<Self>
        where
            F: FnOnce(Option<Self>) -> Result<Option<T>>,
            T: Into<Tree>
    {
        let (mut walker, maybe_child) = unsafe { self.detach(left)? };
        let new_child = f(maybe_child)?.map(|t| t.into());
        walker.tree.own(|t| t.attach(left, new_child));
        Ok(walker)
    }

    /// Similar to `Tree#walk_expect` but yields a `Walker` which fetches from
    /// the same source as `self`.
    pub fn walk_expect<F, T>(self, left: bool, f: F) -> Result<Self>
        where
            F: FnOnce(Self) -> Result<Option<T>>,
            T: Into<Tree>
    {
        let (mut walker, child) = unsafe { self.detach_expect(left)? };
        let new_child = f(child)?.map(|t| t.into());
        walker.tree.own(|t| t.attach(left, new_child));
        Ok(walker)
    }

    /// Returns an immutable reference to the `Tree` wrapped by this walker.
    pub fn tree(&self) -> &Tree {
        &self.tree
    }

    /// Consumes the `Walker` and returns the `Tree` it wraps.
    pub fn into_inner(self) -> Tree {
        self.tree.into_inner()
    }

    /// Takes a `Tree` and returns a `Walker` which fetches from the same source
    /// as `self`.
    fn wrap(&self, tree: Tree) -> Self {
        Walker::new(tree, self.source.clone())
    }

    /// Returns a clone of this `Walker`'s source.
    pub fn clone_source(&self) -> S {
        self.source.clone()
    }

    /// Similar to `Tree#attach`, but can also take a `Walker` since it
    /// implements `Into<Tree`>.
    pub fn attach<T>(mut self, left: bool, maybe_child: Option<T>) -> Self
        where T: Into<Tree>
    {
        self.tree.own(|t| {
            t.attach(left, maybe_child.map(|t| t.into()))
        });
        self
    }

    /// Similar to `Tree#with_value`.
    pub fn with_value(mut self, value: Value) -> Self {
        self.tree.own(|t| t.with_value(value));
        self
    }
}

impl<S> From<Walker<S>> for Tree
    where S: Fetch + Sized + Clone + Send
{
    fn from(walker: Walker<S>) -> Tree {
        walker.into_inner()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::NoopCommit;
    use crate::tree::Tree;

    #[derive(Clone)]
    struct MockSource {}

    impl Fetch for MockSource {
        fn fetch(&self, link: &Link) -> Result<Tree> {
            Ok(Tree::new(link.key().to_vec(), b"foo".to_vec()))
        }
    }

    #[test]
    fn walk_modified() {
        let tree = Tree::new(
                b"test".to_vec(),
                b"abc".to_vec()
            )
            .attach(true, Some(Tree::new(
                b"foo".to_vec(),
                b"bar".to_vec()
            )));

        let source = MockSource {};
        let walker = Walker::new(tree, source);

        let walker = walker.walk(true, |child| -> Result<Option<Tree>> {
            assert_eq!(child.expect("should have child").tree().key(), b"foo");
            Ok(None)
        }).expect("walk failed");
        assert!(walker.into_inner().child(true).is_none());
    }

    #[test]
    fn walk_stored() {
        let mut tree = Tree::new(
                b"test".to_vec(),
                b"abc".to_vec()
            )
            .attach(true, Some(Tree::new(
                b"foo".to_vec(),
                b"bar".to_vec()
            )));
        tree.commit(&mut NoopCommit {})
            .expect("commit failed");

        let source = MockSource {};
        let walker = Walker::new(tree, source);

        let walker = walker.walk(true, |child| -> Result<Option<Tree>> {
            assert_eq!(child.expect("should have child").tree().key(), b"foo");
            Ok(None)
        }).expect("walk failed");
        assert!(walker.into_inner().child(true).is_none());
    }

    #[test]
    fn walk_pruned() {
        let tree = Tree::from_fields(
            b"test".to_vec(),
            b"abc".to_vec(),
            Default::default(),
            Some(Link::Pruned {
                hash: Default::default(),
                key: b"foo".to_vec(),
                child_heights: (0, 0)
            }),
            None
        );

        let source = MockSource {};
        let walker = Walker::new(tree, source);

        let walker = walker.walk_expect(true, |child| -> Result<Option<Tree>> {
            assert_eq!(child.tree().key(), b"foo");
            Ok(None)
        }).expect("walk failed");
        assert!(walker.into_inner().child(true).is_none());
    }
    
    #[test]
    fn walk_none() {
        let tree = Tree::new(
            b"test".to_vec(),
            b"abc".to_vec()
        );

        let source = MockSource {};
        let walker = Walker::new(tree, source);

        walker.walk(true, |child| -> Result<Option<Tree>> {
            assert!(child.is_none());
            Ok(None)
        }).expect("walk failed");
    }
}

