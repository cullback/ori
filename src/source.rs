use std::cell::RefCell;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct FileId(pub usize);

struct SourceFile {
    path: String,
    content: String,
}

/// An arena that owns all source texts.
///
/// Uses `RefCell` so that `add()` can be called with `&self`, avoiding
/// conflicts with outstanding `&str` borrows from `content()`. Each file
/// is heap-allocated (in a `Box`) so its heap address is stable across
/// `add()` calls.
pub struct SourceArena {
    #[allow(clippy::vec_box)]
    files: RefCell<Vec<Box<SourceFile>>>,
}

impl SourceArena {
    pub const fn new() -> Self {
        Self {
            files: RefCell::new(Vec::new()),
        }
    }

    pub fn add(&self, path: String, content: String) -> FileId {
        let mut files = self.files.borrow_mut();
        let id = FileId(files.len());
        files.push(Box::new(SourceFile { path, content }));
        id
    }

    /// Get the content of a file.
    ///
    /// # Safety rationale
    /// Each `SourceFile` is `Box`-allocated, so its heap address is stable
    /// even when the `Vec` grows. The arena never removes or replaces files,
    /// so the returned `&str` remains valid for the lifetime of `&self`.
    pub fn content(&self, id: FileId) -> &str {
        let files = self.files.borrow();
        let ptr: *const str = &raw const *files[id.0].content;
        // SAFETY: The Box ensures stable heap address; arena is append-only.
        unsafe { &*ptr }
    }

    /// Get the path of a file.
    pub fn path(&self, id: FileId) -> &str {
        let files = self.files.borrow();
        let ptr: *const str = &raw const *files[id.0].path;
        // SAFETY: Same as content() — Box ensures stable heap address.
        unsafe { &*ptr }
    }
}
