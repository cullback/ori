use crate::source::SourceArena;
use crate::syntax::ast::Span;

/// A compiler error with an optional source location.
#[derive(Debug)]
pub struct CompileError {
    pub message: String,
    pub span: Option<Span>,
}

impl CompileError {
    pub fn new<M: Into<String>>(message: M) -> Self {
        Self {
            message: message.into(),
            span: None,
        }
    }

    pub fn at<M: Into<String>>(span: Span, message: M) -> Self {
        Self {
            message: message.into(),
            span: Some(span),
        }
    }

    /// Format the error with source context (line, column, carets).
    #[expect(clippy::arithmetic_side_effects, reason = "line/col counting")]
    pub fn format(&self, arena: &SourceArena) -> String {
        let Some(span) = self.span else {
            return self.message.clone();
        };
        let source = arena.content(span.file);
        let path = arena.path(span.file);
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
        let location = if path.is_empty() {
            String::new()
        } else {
            format!("{path}:")
        };
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
