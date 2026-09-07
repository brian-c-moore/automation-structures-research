//! `Value` — the small cross-language data type shared by every corpus
//! composition and its Python oracle. Hand-rolled JSON keeps the crate
//! dependency-light and the encoding inspectable.

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Str(String),
    List(Vec<Value>),
}

impl Value {
    pub fn ints(v: &[i64]) -> Value {
        Value::List(v.iter().map(|x| Value::Int(*x)).collect())
    }
    pub fn as_int(&self) -> i64 {
        match self {
            Value::Int(i) => *i,
            Value::Bool(b) => *b as i64,
            _ => panic!("not int"),
        }
    }
    pub fn as_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            _ => panic!("not bool"),
        }
    }
    pub fn as_list(&self) -> &[Value] {
        match self {
            Value::List(l) => l,
            _ => panic!("not list"),
        }
    }
    pub fn as_int_vec(&self) -> Vec<i64> {
        self.as_list().iter().map(|x| x.as_int()).collect()
    }
    pub fn as_str(&self) -> &str {
        match self {
            Value::Str(s) => s,
            _ => panic!("not str"),
        }
    }

    /// Minimal JSON encoder (objects are not needed: the wire format is
    /// just a JSON value).
    pub fn to_json(&self) -> String {
        match self {
            Value::Int(i) => i.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Str(s) => format!("{:?}", s), // Rust Debug == JSON string for ASCII
            Value::List(l) => {
                let inner: Vec<String> = l.iter().map(|v| v.to_json()).collect();
                format!("[{}]", inner.join(","))
            }
        }
    }

    /// Minimal JSON parser for the `Value` subset (ints, bools, strings,
    /// arrays). Sufficient for every corpus algorithm's I/O.
    pub fn from_json(s: &str) -> Value {
        let bytes: Vec<char> = s.chars().collect();
        let mut pos = 0usize;
        let v = parse(&bytes, &mut pos);
        v
    }
}

fn skip_ws(b: &[char], p: &mut usize) {
    while *p < b.len() && b[*p].is_whitespace() {
        *p += 1;
    }
}

fn parse(b: &[char], p: &mut usize) -> Value {
    skip_ws(b, p);
    match b[*p] {
        '[' => {
            *p += 1;
            let mut list = Vec::new();
            skip_ws(b, p);
            if b[*p] == ']' {
                *p += 1;
                return Value::List(list);
            }
            loop {
                list.push(parse(b, p));
                skip_ws(b, p);
                match b[*p] {
                    ',' => {
                        *p += 1;
                    }
                    ']' => {
                        *p += 1;
                        break;
                    }
                    c => panic!("json: expected , or ] got {c}"),
                }
            }
            Value::List(list)
        }
        '"' => {
            *p += 1;
            let mut s = String::new();
            while b[*p] != '"' {
                if b[*p] == '\\' {
                    *p += 1;
                }
                s.push(b[*p]);
                *p += 1;
            }
            *p += 1;
            Value::Str(s)
        }
        't' => {
            *p += 4;
            Value::Bool(true)
        }
        'f' => {
            *p += 5;
            Value::Bool(false)
        }
        _ => {
            let start = *p;
            if b[*p] == '-' {
                *p += 1;
            }
            while *p < b.len() && (b[*p].is_ascii_digit()) {
                *p += 1;
            }
            let num: String = b[start..*p].iter().collect();
            Value::Int(num.parse().expect("json: bad int"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn json_roundtrip() {
        let v = Value::List(vec![
            Value::Int(-3),
            Value::Bool(true),
            Value::Str("ab".into()),
            Value::List(vec![Value::Int(1), Value::Int(2)]),
        ]);
        assert_eq!(Value::from_json(&v.to_json()), v);
    }
}
