mod crash_merk;
mod temp_merk;

use std::ops::Range;
use std::convert::TryInto;

use byteorder::{BigEndian, WriteBytesExt};
use rand::prelude::*;
use smallvec::smallvec;

use crate::tree::{
    Tree,
    Key,
    Value,
    Walker,
    NoopCommit,
    Batch,
    Op,
    PanicSource,
    BatchEntry
};

pub use crash_merk::CrashMerk;
pub use temp_merk::TempMerk;

pub fn assert_tree_invariants(tree: &Tree) {
    assert!(tree.balance_factor().abs() < 2);

    let maybe_left = tree.link(true);
    if let Some(left) = maybe_left {
        assert!(left.key() < tree.key());
        assert!(!left.is_modified());
    }

    let maybe_right = tree.link(false);
    if let Some(right) = maybe_right {
        assert!(right.key() > tree.key());
        assert!(!right.is_modified());
    }

    if let Some(left) = tree.child(true) {
        assert_tree_invariants(left);
    }
    if let Some(right) = tree.child(false) {
        assert_tree_invariants(right);
    }
}

pub fn apply_memonly_unchecked(tree: Tree, batch: &Batch) -> Tree {
    let walker = Walker::<PanicSource>::new(tree, PanicSource {});
    let mut tree = Walker::<PanicSource>::apply_to(Some(walker), batch)
        .expect("apply failed")
        .0
        .expect("expected tree");
    tree.commit(&mut NoopCommit {})
        .expect("commit failed");
    tree
}

pub fn apply_memonly(tree: Tree, batch: &Batch) -> Tree {
    let tree = apply_memonly_unchecked(tree, batch);
    assert_tree_invariants(&tree);
    tree
}

pub fn apply_to_memonly(maybe_tree: Option<Tree>, batch: &Batch) -> Option<Tree> {
    let maybe_walker = maybe_tree.map(|tree| {
        Walker::<PanicSource>::new(tree, PanicSource {})
    });
    Walker::<PanicSource>::apply_to(maybe_walker, batch)
        .expect("apply failed")
        .0
        .map(|mut tree| {
            tree.commit(&mut NoopCommit {}).expect("commit failed");
            assert_tree_invariants(&tree);
            tree
        })
}

pub fn seq_key(n: u64) -> Key {
    n.to_be_bytes()[..].into()
}

pub fn put_entry(n: u64) -> BatchEntry {
    (seq_key(n), Op::Put(smallvec![123; 60]))
}

pub fn del_entry(n: u64) -> BatchEntry {
    (seq_key(n), Op::Delete)
}

pub fn make_batch_seq(range: Range<u64>) -> Vec<BatchEntry> {
    let mut batch = Vec::with_capacity(
        (range.end - range.start).try_into().unwrap()
    );
    for n in range {
        batch.push(put_entry(n));
    }
    batch
}

pub fn make_del_batch_seq(range: Range<u64>) -> Vec<BatchEntry> {
    let mut batch = Vec::with_capacity(
        (range.end - range.start).try_into().unwrap()
    );
    for n in range {
        batch.push(del_entry(n));
    }
    batch
}

pub fn make_batch_rand(size: u64, seed: u64) -> Vec<BatchEntry> {
    let mut rng: SmallRng = SeedableRng::seed_from_u64(seed);
    let mut batch = Vec::with_capacity(size.try_into().unwrap());
    for _ in 0..size {
        let n = rng.gen::<u64>();
        batch.push(put_entry(n));
    }
    batch.sort_by(|a, b| a.0.cmp(&b.0));
    batch
}

pub fn make_del_batch_rand(size: u64, seed: u64) -> Vec<BatchEntry> {
    let mut rng: SmallRng = SeedableRng::seed_from_u64(seed);
    let mut batch = Vec::with_capacity(size.try_into().unwrap());
    for _ in 0..size {
        let n = rng.gen::<u64>();
        batch.push(del_entry(n));
    }
    batch.sort_by(|a, b| a.0.cmp(&b.0));
    batch
}

pub fn make_tree_rand(
    node_count: u64,
    batch_size: u64,
    initial_seed: u64
) -> Tree {
    assert!(node_count >= batch_size);
    assert!((node_count % batch_size) == 0);

    let value = smallvec![123; 60];
    let mut tree = Tree::new(smallvec![0; 20], value.clone());

    let mut seed = initial_seed;
    
    let batch_count = node_count / batch_size;
    for _ in 0..batch_count {
        let batch = make_batch_rand(batch_size, seed);
        tree = apply_memonly(tree, &batch);
        seed += 1;
    }

    tree
}

pub fn make_tree_seq(node_count: u64) -> Tree {
    let batch_size = if node_count >= 10_000 {
        assert!(node_count % 10_000 == 0);
        10_000
    } else {
        node_count
    };

    let value = smallvec![123; 60];
    let mut tree = Tree::new(smallvec![0; 20], value.clone());
    
    let batch_count = node_count / batch_size;
    for i in 0..batch_count {
        let batch = make_batch_seq((i * batch_size)..((i+1) * batch_size));
        tree = apply_memonly(tree, &batch);
    }

    tree
}
