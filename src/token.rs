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

#[expect(
    clippy::arithmetic_side_effects,
    clippy::too_many_lines,
    reason = "scanner is a single match over character classes — splitting would fragment the logic"
)]
pub fn tokenize(source: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let bytes = source.as_bytes();
    let mut pos = 0;

    while pos < bytes.len() {
        let b = bytes[pos];
        match b {
            // Skip spaces and tabs
            b' ' | b'\t' | b'\r' => pos += 1,

            // Newlines (collapse consecutive)
            b'\n' => {
                if !matches!(tokens.last(), Some(Token::Newline)) {
                    tokens.push(Token::Newline);
                }
                pos += 1;
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
                tokens.push(Token::EqEq);
                pos += 2;
            }
            b'!' if pos + 1 < bytes.len() && bytes[pos + 1] == b'=' => {
                tokens.push(Token::BangEq);
                pos += 2;
            }
            b'-' if pos + 1 < bytes.len() && bytes[pos + 1] == b'>' => {
                tokens.push(Token::Arrow);
                pos += 2;
            }

            // Single-character tokens
            b'=' => {
                tokens.push(Token::Eq);
                pos += 1;
            }
            b':' => {
                tokens.push(Token::Colon);
                pos += 1;
            }
            b'|' => {
                tokens.push(Token::Pipe);
                pos += 1;
            }
            b'(' => {
                tokens.push(Token::LParen);
                pos += 1;
            }
            b')' => {
                tokens.push(Token::RParen);
                pos += 1;
            }
            b'[' => {
                tokens.push(Token::LBracket);
                pos += 1;
            }
            b']' => {
                tokens.push(Token::RBracket);
                pos += 1;
            }
            b',' => {
                tokens.push(Token::Comma);
                pos += 1;
            }
            b'.' => {
                tokens.push(Token::Dot);
                pos += 1;
            }
            b'_' if pos + 1 >= bytes.len() || !bytes[pos + 1].is_ascii_alphanumeric() => {
                tokens.push(Token::Underscore);
                pos += 1;
            }
            b'*' => {
                tokens.push(Token::Star);
                pos += 1;
            }
            b'+' => {
                tokens.push(Token::Plus);
                pos += 1;
            }
            b'-' => {
                tokens.push(Token::Minus);
                pos += 1;
            }
            b'/' => {
                tokens.push(Token::Slash);
                pos += 1;
            }
            b'%' => {
                tokens.push(Token::Percent);
                pos += 1;
            }

            // Integer literals
            b'0'..=b'9' => {
                let start = pos;
                while pos < bytes.len() && bytes[pos].is_ascii_digit() {
                    pos += 1;
                }
                let text = &source[start..pos];
                let n: i64 = text
                    .parse()
                    .unwrap_or_else(|e| panic!("invalid integer literal '{text}': {e}"));
                tokens.push(Token::IntLit(n));
            }

            // Identifiers and keywords
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                let start = pos;
                while pos < bytes.len()
                    && (bytes[pos].is_ascii_alphanumeric() || bytes[pos] == b'_')
                {
                    pos += 1;
                }
                let word = &source[start..pos];
                let tok = match word {
                    "if" => Token::If,
                    "then" => Token::Then,
                    "else" => Token::Else,
                    "fold" => Token::Fold,
                    _ => Token::Ident(word.to_owned()),
                };
                tokens.push(tok);
            }

            _ => panic!("unexpected character '{}' at position {pos}", b as char),
        }
    }

    tokens.push(Token::Eof);
    tokens
}
