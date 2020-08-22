use std::cell::Cell;
use std::collections::LinkedList;
use std::path::{Path, PathBuf};

use failure::{bail, format_err};
use rocksdb::ColumnFamilyDescriptor;
use smallvec::{SmallVec, smallvec};

use crate::error::Result;
use crate::tree::{
    Tree,
    Key,
    Value,
    Op,
    Link,
    Fetch,
    Walker,
    RefWalker,
    Commit,
    Batch,
    Hash,
    NULL_HASH
};
use crate::proofs::encode_into;

const ROOT_KEY_KEY: [u8; 4] = *b"root";

/// A handle to a Merkle key/value store backed by RocksDB.
pub struct Merk {
    tree: Cell<Option<Tree>>,
    db: rocksdb::DB,
    path: PathBuf
}

impl Merk {
    /// Opens a store with the specified file path. If no store exists at that
    /// path, one will be created.
    pub fn open<P: AsRef<Path>>(path: P) -> Result<Merk> {
        let db_opts = Merk::default_db_opts();
        Merk::open_opt(path, db_opts)
    }

    /// Opens a store with the specified file path and the given options. If no
    /// store exists at that path, one will be created.
    pub fn open_opt<P>(path: P, db_opts: rocksdb::Options) -> Result<Merk>
        where P: AsRef<Path>
    {
        let mut path_buf = PathBuf::new();
        path_buf.push(path);
        let cfs = vec![
            // TODO: clone opts or take args
            ColumnFamilyDescriptor::new("aux", Merk::default_db_opts()),
            ColumnFamilyDescriptor::new("internal", Merk::default_db_opts())
        ];
        let db = rocksdb::DB::open_cf_descriptors(&db_opts, &path_buf, cfs)?;

        // try to load root node
        let internal_cf = db.cf_handle("internal").unwrap();
        let tree = match db.get_pinned_cf(internal_cf, ROOT_KEY_KEY)? {
            Some(root_key) => Some(fetch_existing_node(&db, &root_key)?),
            None => None
        };
        let tree = Cell::new(tree);

        Ok(Merk { tree, db, path: path_buf })
    }

    pub fn default_db_opts() -> rocksdb::Options {
        let mut opts = rocksdb::Options::default();
        opts.create_if_missing(true);
        opts.increase_parallelism(num_cpus::get() as i32);
        // opts.set_advise_random_on_open(false);
        opts.set_allow_mmap_writes(true);
        opts.set_allow_mmap_reads(true);
        opts.create_missing_column_families(true);
        opts.set_atomic_flush(true);
        // TODO: tune
        opts
    }

    /// Gets an auxiliary value. 
    pub fn get_aux(&self, key: &[u8]) -> Result<Option<Value>> {
        let aux_cf = self.db.cf_handle("aux");
        let value = self.db.get_pinned_cf(aux_cf.unwrap(), key)?
            .map(|value| value.as_ref().into());
        Ok(value)
    }

    /// Gets a value for the given key. If the key is not found, `None` is
    /// returned.
    ///
    /// Note that this is essentially the same as a normal RocksDB `get`, so
    /// should be a fast operation and has almost no tree overhead.
    pub fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        self.use_tree(|maybe_tree| {
            let mut cursor = match maybe_tree {
                None => return Ok(None), // empty tree
                Some(tree) => tree
            };

            loop {
                if key == cursor.key() {
                    return Ok(Some(cursor.value().to_vec()));
                }

                let left = key < cursor.key();
                let link = match cursor.link(left) {
                    None => return Ok(None), // not found
                    Some(link) => link
                };

                let maybe_child = link.tree();
                match maybe_child {
                    None => break, // value is pruned, fall back to fetching from disk
                    Some(child) => cursor = child // traverse to child
                }
            }

            // TODO: ignore other fields when reading from node bytes
            fetch_node(&self.db, key)
                .map(|maybe_node| {
                    maybe_node.map(|node| node.value().to_vec())
                })
        })
    }

    /// Returns the root hash of the tree (a digest for the entire store which
    /// proofs can be checked against). If the tree is empty, returns the null
    /// hash (zero-filled).
    pub fn root_hash(&self) -> Hash {
        self.use_tree(|tree| tree.map_or(NULL_HASH, |tree| tree.hash()))
    }

    /// Applies a batch of operations (puts and deletes) to the tree.
    ///
    /// This will fail if the keys in `batch` are not sorted and unique. This
    /// check creates some overhead, so if you are sure your batch is sorted and
    /// unique you can use the unsafe `apply_unchecked` for a small performance
    /// gain.
    ///
    /// # Example
    /// ```
    /// # use smallvec::smallvec as vec;
    /// # let mut store = merk::test_utils::TempMerk::new().unwrap();
    /// # store.apply(&[(vec![4,5,6], Op::Put(vec![0]))], &[]).unwrap();
    /// 
    /// use merk::Op;
    ///
    /// let batch = &[
    ///     (vec![1, 2, 3], Op::Put(vec![4, 5, 6])), // puts value [4,5,6] to key [1,2,3]
    ///     (vec![4, 5, 6], Op::Delete) // deletes key [4,5,6]
    /// ];
    /// store.apply(batch, &[]).unwrap();
    /// ```
    pub fn apply(&mut self, batch: &Batch, aux: &Batch) -> Result<()> {
        // ensure keys in batch are sorted and unique
        let mut maybe_prev_key: Option<Key> = None;
        for (key, _) in batch.iter() {
            if let Some(prev_key) = maybe_prev_key {
                if prev_key.as_slice() > key.as_slice() {
                    bail!("Keys in batch must be sorted");
                } else if prev_key.as_slice() == key.as_slice() {
                    bail!("Keys in batch must be unique");
                }
            }
            maybe_prev_key = Some(key.clone());
        }

        unsafe { self.apply_unchecked(batch, aux) }
    }


    /// Applies a batch of operations (puts and deletes) to the tree.
    ///
    /// This is unsafe because the keys in `batch` must be sorted and unique -
    /// if they are not, there will be undefined behavior. For a safe version of
    /// this method which checks to ensure the batch is sorted and unique, see
    /// `apply`.
    ///
    /// # Example
    /// ```
    /// # use smallvec::smallvec as vec;
    /// # let mut store = merk::test_utils::TempMerk::new().unwrap();
    /// # store.apply(&[(vec![4,5,6], Op::Put(vec![0]))], &[]).unwrap();
    /// 
    /// use merk::Op;
    ///
    /// let batch = &[
    ///     (vec![1, 2, 3], Op::Put(vec![4, 5, 6])), // puts value [4,5,6] to key [1,2,3]
    ///     (vec![4, 5, 6], Op::Delete) // deletes key [4,5,6]
    /// ];
    /// unsafe { store.apply_unchecked(batch, &[]).unwrap() };
    /// ```
    pub unsafe fn apply_unchecked(&mut self, batch: &Batch, aux: &Batch) -> Result<()> {
        let maybe_walker = self.tree.take().take()
            .map(|tree| Walker::new(tree, self.source()));

        let (maybe_tree, deleted_keys) = Walker::apply_to(maybe_walker, batch)?;
        self.tree.set(maybe_tree);

        // commit changes to db
        self.commit(deleted_keys, aux)
    }

    /// Closes the store and deletes all data from disk.
    pub fn destroy(self) -> Result<()> {
        let opts = Merk::default_db_opts();
        let path = self.path.clone();
        drop(self);
        rocksdb::DB::destroy(&opts, path)?;
        Ok(())
    }

    /// Creates a Merkle proof for the list of queried keys. For each key in the
    /// query, if the key is found in the store then the value will be proven to
    /// be in the tree. For each key in the query that does not exist in the
    /// tree, its absence will be proven by including boundary keys.
    ///
    /// The proof returned is in an encoded format which can be verified with
    /// `merk::verify`.
    ///
    /// This will fail if the keys in `query` are not sorted and unique. This
    /// check adds some overhead, so if you are sure your batch is sorted and
    /// unique you can use the unsafe `prove_unchecked` for a small performance
    /// gain.
    pub fn prove(&self, query: &[Key]) -> Result<Vec<u8>> {
        // ensure keys in query are sorted and unique
        let mut maybe_prev_key: Option<Key> = None;
        for key in query.iter() {
            if let Some(prev_key) = maybe_prev_key {
                if prev_key.as_slice() > key.as_slice() {
                    bail!("Keys in query must be sorted");
                } else if prev_key.as_slice() == key.as_slice() {
                    bail!("Keys in query must be unique");
                }
            }
            maybe_prev_key = Some(key.clone());
        }

        unsafe { self.prove_unchecked(query) }
    }

    /// Creates a Merkle proof for the list of queried keys. For each key in the
    /// query, if the key is found in the store then the value will be proven to
    /// be in the tree. For each key in the query that does not exist in the
    /// tree, its absence will be proven by including boundary keys.
    ///
    /// The proof returned is in an encoded format which can be verified with
    /// `merk::verify`.
    ///
    /// This is unsafe because the keys in `query` must be sorted and unique -
    /// if they are not, there will be undefined behavior. For a safe version of
    /// this method which checks to ensure the batch is sorted and unique, see
    /// `prove`.
    pub unsafe fn prove_unchecked(&self, query: &[Key]) -> Result<Vec<u8>> {
        self.use_tree_mut(|maybe_tree| {
            let tree = match maybe_tree {
                None => bail!("Cannot create proof for empty tree"),
                Some(tree) => tree
            };

            let mut ref_walker = RefWalker::new(tree, self.source());
            let (proof, _) = ref_walker.create_proof(query)?;

            let mut bytes = Vec::with_capacity(128);
            encode_into(proof.iter(), &mut bytes);
            Ok(bytes)
        })
    }

    pub fn flush(&self) -> Result<()> {
        Ok(self.db.flush()?)
    }

    pub fn commit(&mut self, deleted_keys: LinkedList<Key>, aux: &Batch) -> Result<()> {
        let internal_cf = self.db.cf_handle("internal").unwrap();
        let aux_cf = self.db.cf_handle("aux").unwrap();

        let mut batch = rocksdb::WriteBatch::default();
        let mut to_batch = self.use_tree_mut(|maybe_tree| -> Result<Vec<(Key, Option<SmallVec<[u8; 256]>>)>> {
            // TODO: concurrent commit
            if let Some(tree) = maybe_tree {
                // TODO: configurable committer
                let mut committer = MerkCommitter::new(tree.height(), 1);
                tree.commit(&mut committer)?;

                // update pointer to root node
                batch.put_cf(internal_cf, ROOT_KEY_KEY, tree.key());

                Ok(committer.batch)
            } else {
                // empty tree, delete pointer to root
                batch.delete_cf(internal_cf, ROOT_KEY_KEY);

                Ok(vec![])
            }
        })?;

        // TODO: move this to MerkCommitter impl?
        for key in deleted_keys {
            to_batch.push((key, None));
        }
        to_batch.sort_by(|a, b| a.0.cmp(&b.0));
        for (key, maybe_value) in to_batch {
            if let Some(value) = maybe_value {
                batch.put(key, value);
            } else {
                batch.delete(key);
            }
        }

        for (key, value) in aux {
            match value {
                Op::Put(value) => batch.put_cf(aux_cf, key, value),
                Op::Delete => batch.delete_cf(aux_cf, key)
            };
        }

        // write to db
        let mut opts = rocksdb::WriteOptions::default();
        opts.set_sync(false);
        // TODO: disable WAL once we can ensure consistency with transactions
        self.db.write_opt(batch, &opts)?;

        Ok(())
    }

    pub fn walk<T>(&self, f: impl FnOnce(Option<RefWalker<MerkSource>>) -> T) -> T {
        let mut tree = self.tree.take();
        let maybe_walker = tree.as_mut().map(|tree| {
            RefWalker::new(tree, self.source())
        });
        let res = f(maybe_walker);
        self.tree.set(tree);
        res
    }

    fn source(&self) -> MerkSource {
        MerkSource { db: &self.db }
    }

    fn use_tree<T>(&self, mut f: impl FnMut(Option<&Tree>) -> T) -> T {
        let tree = self.tree.take();
        let res = f(tree.as_ref());
        self.tree.set(tree);
        res
    }

    fn use_tree_mut<T>(&self, mut f: impl FnMut(Option<&mut Tree>) -> T) -> T {
        let mut tree = self.tree.take();
        let res = f(tree.as_mut());
        self.tree.set(tree);
        res
    }
}

impl Drop for Merk {
    fn drop(&mut self) {
        self.db.flush().unwrap();
    }
}

#[derive(Clone)]
pub struct MerkSource<'a> {
    db: &'a rocksdb::DB
}

impl<'a> Fetch for MerkSource<'a> {
    fn fetch(&self, link: &Link) -> Result<Tree> {
        fetch_existing_node(self.db, link.key())
    }
}

struct MerkCommitter {
    batch: Vec<(Key, Option<SmallVec<[u8; 256]>>)>,
    height: u8,
    levels: u8,
    enc_buf: Vec<u8>
}

impl MerkCommitter {
    fn new(height: u8, levels: u8) -> Self {
        MerkCommitter {
            enc_buf: Vec::with_capacity(256),
            batch: Vec::with_capacity(10000),
            height,
            levels
        }
    }
}

impl Commit for MerkCommitter {
    fn write(&mut self, tree: &Tree) -> Result<()> {
        self.enc_buf.clear();
        tree.encode_into(&mut self.enc_buf);

        let encoded: SmallVec<[u8; 256]> = self.enc_buf[..].into();

        self.batch.push((tree.key().into(), Some(encoded)));
        Ok(())
    }

    fn prune(&self, tree: &Tree) -> (bool, bool) {
        // keep N top levels of tree
        let prune = (self.height - tree.height()) >= self.levels;
        (prune, prune)
    }
}

fn fetch_node(db: &rocksdb::DB, key: &[u8]) -> Result<Option<Tree>> {
    let bytes = db.get_pinned(key)?;
    if let Some(bytes) = bytes {
        Ok(Some(Tree::decode(key, &bytes)?))
    } else {
        Ok(None)
    }
}

fn fetch_existing_node(db: &rocksdb::DB, key: &[u8]) -> Result<Tree> {
    match fetch_node(db, key)? {
        None => bail!("key not found: {:?}", key),
        Some(node) => Ok(node)
    }
}

#[cfg(test)]
mod test {
    use smallvec::smallvec as sv;
    use std::thread;
    use crate::test_utils::*;
    use crate::Op;
    use super::Merk;

    // TODO: Close and then reopen test

    fn assert_invariants(merk: &TempMerk) {
        merk.use_tree(|maybe_tree| {
            let tree = maybe_tree.expect("expected tree");
            assert_tree_invariants(tree);
        })
    }

    #[test]
    fn simple_insert_apply() {
        let batch_size = 20;

        let path = thread::current().name().unwrap().to_owned();
        let mut merk = TempMerk::open(path).expect("failed to open merk");

        let batch = make_batch_seq(0..batch_size);
        merk.apply(&batch, &[]).expect("apply failed");

        assert_invariants(&merk);
        assert_eq!(merk.root_hash(), [217, 218, 163, 74, 119, 133, 165, 247, 140, 194, 85, 70, 28, 33, 61, 148, 118, 231, 134, 111]);
    }

    #[test]
    fn insert_uncached() {
        let batch_size = 20;

        let path = thread::current().name().unwrap().to_owned();
        let mut merk = TempMerk::open(path).expect("failed to open merk");

        let batch = make_batch_seq(0..batch_size);
        merk.apply(&batch, &[]).expect("apply failed");
        assert_invariants(&merk);

        let batch = make_batch_seq(batch_size..(batch_size*2));
        merk.apply(&batch, &[]).expect("apply failed");
        assert_invariants(&merk);
    }

    #[test]
    fn insert_rand() {
        let tree_size = 40;
        let batch_size = 4;

        let path = thread::current().name().unwrap().to_owned();
        let mut merk = TempMerk::open(path).expect("failed to open merk");

        for i in 0..(tree_size / batch_size) {
            println!("i:{}", i);
            let batch = make_batch_rand(batch_size, i);
            merk.apply(&batch, &[]).expect("apply failed");

        }
    }

    #[test]
    fn actual_deletes() {
        let path = thread::current().name().unwrap().to_owned();
        let mut merk = TempMerk::open(path).expect("failed to open merk");

        let batch = make_batch_rand(10, 1);
        merk.apply(&batch, &[]).expect("apply failed");

        let key = batch.first().unwrap().0.clone();
        merk.apply(&[ (key.clone(), Op::Delete) ], &[]).unwrap();

        let value = merk.db.get(key.as_slice()).unwrap();
        assert!(value.is_none());
    }

    #[test]
    fn aux_data() {
        let path = thread::current().name().unwrap().to_owned();
        let mut merk = TempMerk::open(path).expect("failed to open merk");
        merk.apply(&[], &[(sv![1,2,3], Op::Put(sv![4,5,6]))]).expect("apply failed");
        let val = merk.get_aux(&[1,2,3]).unwrap();
        assert_eq!(val, Some(sv![4,5,6]));
    }

    #[test]
    fn simulated_crash() {
        let path = thread::current().name().unwrap().to_owned();
        let mut merk = CrashMerk::open(path).expect("failed to open merk");

        merk.apply(
            &[(sv![0], Op::Put(sv![1]))],
            &[(sv![2], Op::Put(sv![3]))]
        ).expect("apply failed");

        // make enough changes so that main column family gets auto-flushed
        for i in 0..250 {
            merk.apply(
                &make_batch_seq(i * 2_000..(i + 1) * 2_000),
                &[]
            ).expect("apply failed");
        }

        merk.crash().unwrap();

        assert_eq!(merk.get_aux(&[2]).unwrap(), Some(sv![3]));
        merk.destroy().unwrap();
    }

    #[test]
    fn get_not_found() {
        let path = thread::current().name().unwrap().to_owned();
        let mut merk = TempMerk::open(path).expect("failed to open merk");

        // no root
        assert!(merk.get(&[1, 2, 3]).unwrap().is_none());

        // cached
        merk.apply(&[(sv![5, 5, 5], Op::Put(sv![]))], &[]).unwrap();
        assert!(merk.get(&[1, 2, 3]).unwrap().is_none());

        // uncached
        merk.apply(&[
            (sv![0, 0, 0], Op::Put(sv![])),
            (sv![1, 1, 1], Op::Put(sv![])),
            (sv![2, 2, 2], Op::Put(sv![]))
        ], &[]).unwrap();
        assert!(merk.get(&[3, 3, 3]).unwrap().is_none());
    }
} 
