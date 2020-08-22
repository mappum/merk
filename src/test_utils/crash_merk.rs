use std::env::temp_dir;
use std::fs;
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};
use std::path::Path;
use std::time::SystemTime;
use crate::{Merk, Result};

/// Wraps a Merk instance and drops it without flushing once it goes out of
/// scope.
pub struct CrashMerk {
    inner: Option<ManuallyDrop<Merk>>,
    path: Box<Path>
}

impl CrashMerk {
    /// Opens a `CrashMerk` at the given file path, creating a new one if it does
    /// not exist.
    pub fn open<P: AsRef<Path>>(path: P) -> Result<CrashMerk> {
        let merk = Merk::open(&path)?;
        let inner = Some(ManuallyDrop::new(merk));
        Ok(CrashMerk { inner, path: path.as_ref().into() })
    }

    pub fn crash(&mut self) -> Result<()> {
        drop(self.inner.take().unwrap());

        // rename to invalidate rocksdb's lock
        let file_name = format!(
            "{}_crashed",
            self.path.file_name()
                .unwrap()
                .to_str()
                .unwrap()
        );
        let mut new_path = self.path.with_file_name(file_name);
        fs::rename(&self.path, &new_path)?;

        let mut new_merk = CrashMerk::open(&new_path)?;
        self.inner = new_merk.inner.take();
        self.path = new_merk.path;
        Ok(())
    }

    pub fn into_inner(self) -> Merk {
        ManuallyDrop::into_inner(self.inner.unwrap())
    }

    pub fn destroy(self) -> Result<()> {
        self.into_inner().destroy()
    }
}

impl Deref for CrashMerk {
    type Target = Merk;

    fn deref(&self) -> &Merk {
        self.inner.as_ref().unwrap()
    }
}

impl DerefMut for CrashMerk {
    fn deref_mut(&mut self) -> &mut Merk {
        self.inner.as_mut().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use smallvec::smallvec as vec;
    use super::super::TempMerk;
    use super::CrashMerk;
    use crate::Op;

    #[test]
    #[ignore] // currently this still works because we enabled the WAL
    fn crash() {
        let path = std::thread::current().name().unwrap().to_owned();

        let mut merk = CrashMerk::open(&path).expect("failed to open merk");
        merk.apply(&[(vec![1,2,3], Op::Put(vec![4,5,6]))], &[]).expect("apply failed");
        merk.crash().unwrap();
        assert_eq!(merk.get(&[1,2,3]).expect("failed to get"), None);
        merk.into_inner().destroy().unwrap();
    }
}
