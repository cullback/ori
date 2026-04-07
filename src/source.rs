#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct FileId(pub usize);

/// An arena that owns all source texts.
///
/// Source strings are leaked (`Box::leak`) so that `&str` references
/// are valid for `'static`. This is fine for a compiler — it runs once,
/// allocates source texts, and exits.
pub struct SourceArena {
    files: Vec<(&'static str, &'static str)>, // (path, content)
}

impl SourceArena {
    pub const fn new() -> Self {
        Self { files: Vec::new() }
    }

    pub fn add(&mut self, path: String, content: String) -> FileId {
        let id = FileId(self.files.len());
        let leaked_path: &'static str = Box::leak(path.into_boxed_str());
        let leaked_content: &'static str = Box::leak(content.into_boxed_str());
        self.files.push((leaked_path, leaked_content));
        id
    }

    pub fn content(&self, id: FileId) -> &'static str {
        self.files[id.0].1
    }

    pub fn path(&self, id: FileId) -> &'static str {
        self.files[id.0].0
    }

    pub fn find_by_path(&self, path: &str) -> Option<FileId> {
        self.files.iter().position(|(p, _)| *p == path).map(FileId)
    }
}
