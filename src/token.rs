#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    Ident(String),
    IntLit(i64),

    // Punctuation
    Eq,
    Colon,
    Pipe,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Arrow,
    Underscore,
    Dot,
    LBrace,
    RBrace,

    // Operators
    Star,
    Plus,
    Minus,
    Slash,
    Percent,
    EqEq,
    BangEq,

    // Keywords
    If,
    Then,
    Else,
    Fold,

    Newline,
    Eof,
}

/// A span into source text, identified by byte offset and length.
#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub len: usize,
}

impl Span {
    pub const fn new(start: usize, len: usize) -> Self {
        Self { start, len }
    }

    /// Format a diagnostic with source context and underline.
    #[expect(
        clippy::arithmetic_side_effects,
        reason = "offset arithmetic on bounded source text"
    )]
    pub fn display(&self, source: &str, msg: &str) -> String {
        let (line, col) = self.line_col(source);
        let src_line = self.source_line(source);
        let pad = " ".repeat(col - 1);
        let carets = "^".repeat(self.len.max(1));
        let gutter = format!("{line:>3} | ");
        let blank = "    | ";
        format!(
            " --> {line}:{col}\n{blank}\n{gutter}{src_line}\n{blank}{pad}{carets}\n{blank}{msg}"
        )
    }

    #[expect(
        clippy::arithmetic_side_effects,
        reason = "line/col counting on bounded source text"
    )]
    fn line_col(&self, source: &str) -> (usize, usize) {
        let mut line = 1;
        let mut col = 1;
        for (i, ch) in source.char_indices() {
            if i >= self.start {
                break;
            }
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
        (line, col)
    }

    #[expect(
        clippy::arithmetic_side_effects,
        reason = "offset arithmetic on bounded source text"
    )]
    fn source_line<'a>(&self, source: &'a str) -> &'a str {
        let start = source[..self.start].rfind('\n').map_or(0, |i| i + 1);
        let end = source[self.start..]
            .find('\n')
            .map_or(source.len(), |i| self.start + i);
        &source[start..end]
    }
}

#[expect(
    clippy::arithmetic_side_effects,
    clippy::too_many_lines,
    reason = "scanner is a single match over character classes — splitting would fragment the logic"
)]
pub fn tokenize(source: &str) -> (Vec<Token>, Vec<Span>) {
    let mut tokens = Vec::new();
    let mut spans = Vec::new();
    let bytes = source.as_bytes();
    let mut pos = 0;

    while pos < bytes.len() {
        let at = pos;
        let b = bytes[pos];
        match b {
            // Skip spaces and tabs
            b' ' | b'\t' | b'\r' => pos += 1,

            // Newlines (collapse consecutive)
            b'\n' => {
                pos += 1;
                if !matches!(tokens.last(), Some(Token::Newline)) {
                    spans.push(Span::new(at, 1));
                    tokens.push(Token::Newline);
                }
            }

            // Line comments
            b'/' if pos + 1 < bytes.len() && bytes[pos + 1] == b'/' => {
                pos += 2;
                while pos < bytes.len() && bytes[pos] != b'\n' {
                    pos += 1;
                }
            }

            // Two-character tokens
            b'=' if pos + 1 < bytes.len() && bytes[pos + 1] == b'=' => {
                pos += 2;
                spans.push(Span::new(at, 2));
                tokens.push(Token::EqEq);
            }
            b'!' if pos + 1 < bytes.len() && bytes[pos + 1] == b'=' => {
                pos += 2;
                spans.push(Span::new(at, 2));
                tokens.push(Token::BangEq);
            }
            b'-' if pos + 1 < bytes.len() && bytes[pos + 1] == b'>' => {
                pos += 2;
                spans.push(Span::new(at, 2));
                tokens.push(Token::Arrow);
            }

            // Single-character tokens
            b'=' | b':' | b'|' | b'(' | b')' | b'[' | b']' | b',' | b'.' | b'{' | b'}' | b'*'
            | b'+' | b'-' | b'/' | b'%' => {
                pos += 1;
                let tok = match b {
                    b'=' => Token::Eq,
                    b':' => Token::Colon,
                    b'|' => Token::Pipe,
                    b'(' => Token::LParen,
                    b')' => Token::RParen,
                    b'[' => Token::LBracket,
                    b']' => Token::RBracket,
                    b',' => Token::Comma,
                    b'.' => Token::Dot,
                    b'{' => Token::LBrace,
                    b'}' => Token::RBrace,
                    b'*' => Token::Star,
                    b'+' => Token::Plus,
                    b'-' => Token::Minus,
                    b'/' => Token::Slash,
                    b'%' => Token::Percent,
                    _ => unreachable!(),
                };
                spans.push(Span::new(at, 1));
                tokens.push(tok);
            }
            b'_' if pos + 1 >= bytes.len() || !bytes[pos + 1].is_ascii_alphanumeric() => {
                pos += 1;
                spans.push(Span::new(at, 1));
                tokens.push(Token::Underscore);
            }

            // Integer literals
            b'0'..=b'9' => {
                while pos < bytes.len() && bytes[pos].is_ascii_digit() {
                    pos += 1;
                }
                let text = &source[at..pos];
                let n: i64 = text
                    .parse()
                    .unwrap_or_else(|e| panic!("invalid integer literal '{text}': {e}"));
                spans.push(Span::new(at, pos - at));
                tokens.push(Token::IntLit(n));
            }

            // Identifiers and keywords
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                while pos < bytes.len()
                    && (bytes[pos].is_ascii_alphanumeric() || bytes[pos] == b'_')
                {
                    pos += 1;
                }
                let word = &source[at..pos];
                let tok = match word {
                    "if" => Token::If,
                    "then" => Token::Then,
                    "else" => Token::Else,
                    "fold" => Token::Fold,
                    _ => Token::Ident(word.to_owned()),
                };
                spans.push(Span::new(at, pos - at));
                tokens.push(tok);
            }

            _ => panic!("unexpected character '{}' at position {pos}", b as char),
        }
    }

    spans.push(Span::new(pos, 0));
    tokens.push(Token::Eof);
    (tokens, spans)
}
