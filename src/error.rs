use crate::syntax::ast::Span;

/// A compiler error with an optional source location.
#[derive(Debug)]
pub struct CompileError {
    pub message: String,
    pub span: Option<Span>,
    /// Source text for the span (when different from the main file, e.g. imported modules).
    pub source: Option<String>,
    /// File path for the span (when from an imported file).
    pub file: Option<String>,
}

impl CompileError {
    pub fn new<M: Into<String>>(message: M) -> Self {
        Self {
            message: message.into(),
            span: None,
            source: None,
            file: None,
        }
    }

    pub fn at<M: Into<String>>(span: Span, message: M) -> Self {
        Self {
            message: message.into(),
            span: Some(span),
            source: None,
            file: None,
        }
    }

    /// Attach the source text and file path for errors from imported modules.
    pub fn in_file(mut self, file: String, source: String) -> Self {
        self.file = Some(file);
        self.source = Some(source);
        self
    }

    /// Format the error with source context (line, column, carets).
    #[expect(clippy::arithmetic_side_effects, reason = "line/col counting")]
    pub fn format(&self, main_source: &str) -> String {
        let Some(span) = self.span else {
            return self.message.clone();
        };
        // Use the error's own source if available, otherwise the main source
        let source = self.source.as_deref().unwrap_or(main_source);
        if span.start >= source.len() || span.end > source.len() {
            return self.message.clone();
        }
        let mut line = 1_usize;
        let mut col = 1_usize;
        for (i, ch) in source.char_indices() {
            if i >= span.start {
                break;
            }
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
        let line_start = source[..span.start].rfind('\n').map_or(0_usize, |i| i + 1);
        let line_end = source[span.start..]
            .find('\n')
            .map_or(source.len(), |i| span.start + i);
        let src_line = &source[line_start..line_end];
        let pad = " ".repeat(col - 1);
        let carets = "^".repeat((span.end - span.start).max(1));
        let location = self
            .file
            .as_deref()
            .map_or(String::new(), |f| format!("{f}:"));
        format!(
            "\n --> {location}{line}:{col}\n    | \n{line:>3} | {src_line}\n    | {pad}{carets}\n    | {}",
            self.message
        )
    }
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
