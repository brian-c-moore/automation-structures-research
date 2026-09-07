"""Hashes: idiomatic Python reference oracles.

Independent of the Rust composition under test.
Each oracle uses the stdlib `hashlib` (SHA-256, SHA-3-256) or the
`blake3` PyPI package (BLAKE3). Written without framework awareness —
this is the textbook reference.

Wire format: byte inputs / outputs are hex strings (per the
`Value::Bytes` JSON encoding in `src/value.rs`).
"""
import hashlib

# BLAKE3 uses the exact dependency pinned in requirements.txt. Import
# failure invalidates the comparison and therefore terminates the oracle.
import blake3 as _blake3


def sha256(data_hex):
    data = bytes.fromhex(data_hex) if data_hex else b""
    return hashlib.sha256(data).hexdigest()


def sha3_256(data_hex):
    data = bytes.fromhex(data_hex) if data_hex else b""
    return hashlib.sha3_256(data).hexdigest()


def blake3_hash(data_hex):
    data = bytes.fromhex(data_hex) if data_hex else b""
    return _blake3.blake3(data).hexdigest()


ORACLES = {
    "sha256": sha256,
    "sha3_256": sha3_256,
    "blake3": blake3_hash,
}
