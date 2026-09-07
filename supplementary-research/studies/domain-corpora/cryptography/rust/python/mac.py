"""Message authentication: idiomatic Python reference oracles.

HMAC-SHA-256 uses the stdlib `hmac` module — the textbook reference,
independent of the Rust composition under test.
"""
import hmac
import hashlib


def hmac_sha256(args):
    key_hex, msg_hex = args
    key = bytes.fromhex(key_hex) if key_hex else b""
    msg = bytes.fromhex(msg_hex) if msg_hex else b""
    return hmac.new(key, msg, hashlib.sha256).hexdigest()


ORACLES = {
    "hmac_sha256": hmac_sha256,
}
