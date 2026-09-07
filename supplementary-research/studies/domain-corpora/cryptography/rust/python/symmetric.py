"""Symmetric ciphers: idiomatic Python reference oracles.

Covers ChaCha20, using `pyca/cryptography` for the reference. That
library's ChaCha20 takes a 16-byte nonce that is the 4-byte block
counter (little-endian) prepended to the 12-byte nonce, so the two are
assembled here.

Wire format: byte fields are hex strings; counter is an integer.
"""
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms


def chacha20(args):
    # args = [key_hex, nonce_hex, counter_int, plaintext_hex]
    key_hex, nonce_hex, counter, plaintext_hex = args
    key = bytes.fromhex(key_hex)
    nonce_12 = bytes.fromhex(nonce_hex)
    plaintext = bytes.fromhex(plaintext_hex) if plaintext_hex else b""

    # pyca/cryptography's ChaCha20 nonce is 16 bytes = counter (LE, 4) || nonce (12).
    nonce_16 = (counter & 0xFFFFFFFF).to_bytes(4, "little") + nonce_12

    cipher = Cipher(algorithms.ChaCha20(key, nonce_16), mode=None)
    encryptor = cipher.encryptor()
    return (encryptor.update(plaintext) + encryptor.finalize()).hex()


ORACLES = {
    "chacha20": chacha20,
}
