//! `Value` — the small cross-language data type shared by every corpus
//! composition and its Python oracle. Hand-rolled JSON keeps the crate
//! dependency-light and the encoding inspectable (teaching).
//!
//! **Cryptography extension.** Adds a `Bytes(Vec<u8>)` variant for byte
//! strings (hashes, ciphertexts, MAC tags, signatures, shared secrets).
//! On the wire `Bytes` encodes as a hex-string JSON literal; Python
//! oracles emit and consume hex via `bytes.fromhex` / `.hex()`. The
//! `as_bytes()` accessor reconstitutes a `Vec<u8>` from either
//! `Bytes` (direct) or `Str` (the wire form after a JSON round-trip).

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Str(String),
    Bytes(Vec<u8>),
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
    /// Byte accessor. `Bytes` returns its content directly; `Str` is
    /// interpreted as hex (the wire form of `Bytes` after a JSON
    /// round-trip).
    pub fn as_bytes(&self) -> Vec<u8> {
        match self {
            Value::Bytes(b) => b.clone(),
            Value::Str(s) => hex_decode(s).expect("Value::as_bytes: Str is not valid hex"),
            _ => panic!("not bytes"),
        }
    }
    /// Convenience constructor: parse a hex string into `Value::Bytes`.
    /// Case-insensitive; no `0x` prefix.
    pub fn bytes_hex(s: &str) -> Value {
        Value::Bytes(hex_decode(s).expect("bytes_hex: invalid hex"))
    }

    /// Minimal JSON encoder (objects are not needed: the wire format is
    /// just a JSON value). `Bytes` encodes as a hex-string JSON literal.
    pub fn to_json(&self) -> String {
        match self {
            Value::Int(i) => i.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Str(s) => format!("{:?}", s), // Rust Debug == JSON string for ASCII
            Value::Bytes(b) => format!("{:?}", hex_encode(b)),
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

// ---- Hex codec (used by Value::Bytes JSON encoding) ----

pub fn hex_encode(b: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(b.len() * 2);
    for byte in b {
        s.push(HEX[(byte >> 4) as usize] as char);
        s.push(HEX[(byte & 0x0F) as usize] as char);
    }
    s
}

pub fn hex_decode(s: &str) -> Option<Vec<u8>> {
    let s = s.trim();
    if s.len() % 2 != 0 {
        return None;
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let hi = hex_nibble(bytes[i])?;
        let lo = hex_nibble(bytes[i + 1])?;
        out.push((hi << 4) | lo);
        i += 2;
    }
    Some(out)
}

fn hex_nibble(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
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
    #[test]
    fn bytes_roundtrip_via_hex_str() {
        let b = Value::Bytes(vec![0xDE, 0xAD, 0xBE, 0xEF]);
        let json = b.to_json();
        // After JSON round-trip the wire form is Str, hex-encoded.
        let parsed = Value::from_json(&json);
        assert_eq!(parsed, Value::Str("deadbeef".into()));
        // as_bytes() reconstitutes the byte string from the Str form.
        assert_eq!(parsed.as_bytes(), vec![0xDE, 0xAD, 0xBE, 0xEF]);
        // Direct Bytes value also returns its content.
        assert_eq!(b.as_bytes(), vec![0xDE, 0xAD, 0xBE, 0xEF]);
    }
    #[test]
    fn hex_codec_roundtrip() {
        let bytes: Vec<u8> = (0..=255).collect();
        assert_eq!(hex_decode(&hex_encode(&bytes)), Some(bytes));
    }
}
