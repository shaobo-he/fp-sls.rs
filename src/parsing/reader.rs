//! An s-expression reader for SMT-LIB text. Port of the `string->sexp` reader
//! in `parsing/parse.rkt`, including the custom read-table that turns `#x…` /
//! `#b…` literals into `(_ bvVALUE WIDTH)` constants.

use crate::sexp::Sexp;
use rug::Integer;

struct Reader {
    chars: Vec<char>,
    pos: usize,
}

#[inline]
fn is_delim(c: char) -> bool {
    c.is_whitespace() || matches!(c, '(' | ')' | ';' | '|' | '"')
}

impl Reader {
    fn new(s: &str) -> Reader {
        Reader {
            chars: s.chars().collect(),
            pos: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }
    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn skip_trivia(&mut self) {
        while let Some(c) = self.peek() {
            if c == ';' {
                // Line comment.
                while let Some(c) = self.peek() {
                    self.pos += 1;
                    if c == '\n' {
                        break;
                    }
                }
            } else if c.is_whitespace() {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    /// Read one form, or `None` at end of input.
    fn read_form(&mut self) -> Option<Sexp> {
        self.skip_trivia();
        match self.peek()? {
            '(' => {
                self.bump();
                Some(self.read_list())
            }
            ')' => panic!("unexpected ) in input"),
            '|' => Some(self.read_pipe_symbol()),
            '"' => Some(self.read_string()),
            '#' => Some(self.read_hash()),
            _ => Some(self.read_atom()),
        }
    }

    fn read_list(&mut self) -> Sexp {
        let mut items = Vec::new();
        loop {
            self.skip_trivia();
            match self.peek() {
                None => panic!("unterminated list"),
                Some(')') => {
                    self.bump();
                    break;
                }
                _ => items.push(self.read_form().expect("form inside list")),
            }
        }
        Sexp::List(items)
    }

    fn read_pipe_symbol(&mut self) -> Sexp {
        self.bump(); // opening |
        let mut s = String::new();
        loop {
            match self.bump() {
                None => panic!("unterminated |…| symbol"),
                Some('|') => break,
                Some(c) => s.push(c),
            }
        }
        // Preserve the pipes so the identifier prints/round-trips as written and
        // matches its `declare-fun` form verbatim.
        Sexp::Sym(format!("|{s}|"))
    }

    fn read_string(&mut self) -> Sexp {
        self.bump(); // opening "
        let mut s = String::from("\"");
        loop {
            match self.bump() {
                None => panic!("unterminated string"),
                Some('"') => {
                    // "" is an escaped quote in SMT-LIB.
                    if self.peek() == Some('"') {
                        self.bump();
                        s.push('"');
                    } else {
                        s.push('"');
                        break;
                    }
                }
                Some(c) => s.push(c),
            }
        }
        Sexp::Sym(s)
    }

    fn read_hash(&mut self) -> Sexp {
        self.bump(); // '#'
        match self.bump() {
            Some('x') => {
                let digits = self.take_while(|c| c.is_ascii_hexdigit());
                let value = Integer::from_str_radix(&digits, 16).expect("hex literal");
                build_bvconst(value, 4 * digits.chars().count() as u32)
            }
            Some('b') => {
                let digits = self.take_while(|c| c == '0' || c == '1');
                let value = Integer::from_str_radix(&digits, 2).expect("binary literal");
                build_bvconst(value, digits.chars().count() as u32)
            }
            other => panic!("unsupported # literal: #{other:?}"),
        }
    }

    fn read_atom(&mut self) -> Sexp {
        let token = self.take_while(|c| !is_delim(c) && c != '#');
        // A numeral is a non-empty run of ASCII digits.
        if !token.is_empty() && token.chars().all(|c| c.is_ascii_digit()) {
            Sexp::Int(Integer::from_str_radix(&token, 10).expect("numeral"))
        } else {
            Sexp::Sym(token)
        }
    }

    fn take_while<F: Fn(char) -> bool>(&mut self, pred: F) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if pred(c) {
                s.push(c);
                self.pos += 1;
            } else {
                break;
            }
        }
        s
    }
}

fn build_bvconst(value: Integer, width: u32) -> Sexp {
    Sexp::List(vec![
        Sexp::sym("_"),
        Sexp::sym(format!("bv{value}")),
        Sexp::int(width),
    ])
}

/// `(string->sexp str)` — read every top-level form.
pub fn read_all(s: &str) -> Vec<Sexp> {
    let mut r = Reader::new(s);
    let mut forms = Vec::new();
    while let Some(form) = r.read_form() {
        forms.push(form);
    }
    forms
}

/// `(file->sexp fn)`.
pub fn read_file(path: &str) -> std::io::Result<Vec<Sexp>> {
    let text = std::fs::read_to_string(path)?;
    Ok(read_all(&text))
}
