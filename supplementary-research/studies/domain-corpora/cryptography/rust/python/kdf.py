"""Key-derivation functions: idiomatic Python reference oracles.

HKDF-SHA-256 uses `cryptography.hazmat.primitives.kdf.hkdf`.
PBKDF2-HMAC-SHA-256 uses the stdlib `hashlib.pbkdf2_hmac`.
"""
import hashlib

from cryptography.hazmat.primitives import hashes as crypto_hashes
from cryptography.hazmat.primitives.kdf.hkdf import HKDF


def hkdf_sha256(args):
    # args = [salt_hex, ikm_hex, info_hex, length_int]
    salt_hex, ikm_hex, info_hex, length = args
    salt = bytes.fromhex(salt_hex) if salt_hex else b""
    ikm = bytes.fromhex(ikm_hex) if ikm_hex else b""
    info = bytes.fromhex(info_hex) if info_hex else b""

    # pyca/cryptography HKDF: pass salt=None when empty to mirror the
    # RFC 5869 "salt defaults to HashLen zero bytes" behaviour.
    salt_arg = salt if len(salt) > 0 else None

    hkdf = HKDF(
        algorithm=crypto_hashes.SHA256(),
        length=length,
        salt=salt_arg,
        info=info,
    )
    return hkdf.derive(ikm).hex()


def pbkdf2_hmac_sha256(args):
    # args = [password_hex, salt_hex, iterations_int, length_int]
    pwd_hex, salt_hex, iterations, length = args
    password = bytes.fromhex(pwd_hex) if pwd_hex else b""
    salt = bytes.fromhex(salt_hex) if salt_hex else b""
    return hashlib.pbkdf2_hmac("sha256", password, salt, iterations, length).hex()


ORACLES = {
    "hkdf_sha256": hkdf_sha256,
    "pbkdf2_hmac_sha256": pbkdf2_hmac_sha256,
}
