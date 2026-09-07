#!/usr/bin/env python3
# Fetch and parse a Wycheproof RSA-PSS-SHA-256-MGF1-SaltLen=32 test vector,
# then cross-validate it with Python's cryptography library so the KAT
# we embed in tests/rsa_pss_sha256_kat.rs is independently confirmed
# against two implementations (Wycheproof and cryptography/OpenSSL).

import json
import os
import sys
import urllib.request

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import padding, rsa
from cryptography.hazmat.primitives.asymmetric.rsa import RSAPublicNumbers
from cryptography.exceptions import InvalidSignature

URL = (
    "https://raw.githubusercontent.com/C2SP/wycheproof/main/"
    "testvectors_v1/rsa_pss_2048_sha256_mgf1_32_test.json"
)
LOCAL = os.path.join(os.path.dirname(__file__), "_wycheproof_rsa_pss_2048_sha256.json")


def fetch():
    if not os.path.exists(LOCAL):
        print(f"downloading {URL} ...")
        req = urllib.request.Request(URL, headers={"User-Agent": "ed25519-pyref/1.0"})
        with urllib.request.urlopen(req, timeout=30) as resp:
            data = resp.read()
        with open(LOCAL, "wb") as f:
            f.write(data)
        print(f"saved {len(data)} bytes to {LOCAL}")
    else:
        print(f"using cached {LOCAL}")
    with open(LOCAL, "rb") as f:
        return json.loads(f.read())


def der_int(buf, off):
    # Parses a DER INTEGER at offset `off` in `buf`. Returns (int_value, new_off).
    assert buf[off] == 0x02, f"expected INTEGER tag at off {off}, got {hex(buf[off])}"
    off += 1
    if buf[off] & 0x80:
        n_len_bytes = buf[off] & 0x7f
        off += 1
        length = int.from_bytes(buf[off:off + n_len_bytes], "big")
        off += n_len_bytes
    else:
        length = buf[off]
        off += 1
    val = int.from_bytes(buf[off:off + length], "big", signed=False)
    return val, off + length


def parse_rsa_pubkey_der(der_bytes):
    # SubjectPublicKeyInfo OR raw RSAPublicKey.
    # Wycheproof uses SubjectPublicKeyInfo in the "keyDer" field.
    # We unwrap the outer SEQUENCE / AlgorithmIdentifier / BIT STRING to get
    # the inner RSAPublicKey SEQUENCE, then read its two INTEGERs (n, e).
    off = 0
    assert der_bytes[off] == 0x30, "expected outer SEQUENCE"
    off += 1
    if der_bytes[off] & 0x80:
        n_len_bytes = der_bytes[off] & 0x7f
        off += 1 + n_len_bytes
    else:
        off += 1
    # AlgorithmIdentifier SEQUENCE.
    assert der_bytes[off] == 0x30, "expected algid SEQUENCE"
    off += 1
    if der_bytes[off] & 0x80:
        n_len_bytes = der_bytes[off] & 0x7f
        algid_len = int.from_bytes(der_bytes[off + 1:off + 1 + n_len_bytes], "big")
        off += 1 + n_len_bytes
    else:
        algid_len = der_bytes[off]
        off += 1
    off += algid_len
    # BIT STRING.
    assert der_bytes[off] == 0x03, "expected BIT STRING"
    off += 1
    if der_bytes[off] & 0x80:
        n_len_bytes = der_bytes[off] & 0x7f
        off += 1 + n_len_bytes
    else:
        off += 1
    # Skip the unused-bits byte.
    assert der_bytes[off] == 0x00, "expected 0 unused bits"
    off += 1
    # Inner RSAPublicKey SEQUENCE.
    assert der_bytes[off] == 0x30, "expected inner SEQUENCE"
    off += 1
    if der_bytes[off] & 0x80:
        n_len_bytes = der_bytes[off] & 0x7f
        off += 1 + n_len_bytes
    else:
        off += 1
    n, off = der_int(der_bytes, off)
    e, _ = der_int(der_bytes, off)
    return n, e


def main():
    data = fetch()
    print(f"algorithm = {data.get('algorithm')}")
    print(f"schema    = {data.get('schema')}")
    print(f"number of groups = {len(data.get('testGroups', []))}")

    chosen = None
    for grp in data["testGroups"]:
        # Filter on MGF1+SHA-256 with sLen=32 (the 32-byte salt variant).
        mgf = grp.get("mgf", grp.get("mgfHash", ""))
        sha = grp.get("sha", grp.get("hash", ""))
        sLen = grp.get("sLen", grp.get("saltLength", 0))
        mgfSha = grp.get("mgfSha", sha)  # MGF1 hash; defaults to inner hash
        key_size = grp.get("keySize", 0)
        if "SHA-256" not in str(sha):
            continue
        if str(sLen) != "32":
            continue
        if "SHA-256" not in str(mgfSha):
            continue
        if key_size != 2048:
            continue
        # Wycheproof v1 stores modulus + publicExponent as **hex** strings
        # in publicKey{}. publicExponent "010001" = 65537 (hex), NOT decimal.
        pk_obj = grp.get("publicKey", {})
        n_hex = pk_obj.get("modulus") or grp.get("n")
        e_hex = pk_obj.get("publicExponent") or grp.get("e")
        if n_hex and e_hex is not None:
            n = int(n_hex, 16) if isinstance(n_hex, str) else int(n_hex)
            e = int(e_hex, 16) if isinstance(e_hex, str) else int(e_hex)
        elif grp.get("publicKeyDer"):
            der = bytes.fromhex(grp["publicKeyDer"])
            n, e = parse_rsa_pubkey_der(der)
        else:
            continue
        # Find a "valid" test in this group.
        for tc in grp.get("tests", []):
            if tc.get("result") != "valid":
                continue
            msg_hex = tc["msg"]
            sig_hex = tc["sig"]
            chosen = (n, e, msg_hex, sig_hex, tc["tcId"], tc.get("comment", ""), grp)
            break
        if chosen:
            break

    if chosen is None:
        print("NO MATCHING TEST FOUND")
        sys.exit(2)

    n, e, msg_hex, sig_hex, tc_id, comment, grp = chosen
    print(f"\nselected tcId = {tc_id}  comment = {comment!r}")
    print(f"key_size      = {grp.get('keySize')}")
    print(f"sha           = {grp.get('sha', grp.get('hash'))}")
    print(f"mgf           = {grp.get('mgf', grp.get('mgfHash'))}")
    print(f"sLen          = {grp.get('sLen', grp.get('saltLength'))}")
    print(f"e             = {e}")
    print(f"n  (hex, {(n.bit_length() + 7) // 8} bytes) = {hex(n)}")
    print(f"msg(hex, {len(msg_hex) // 2} bytes) = {msg_hex}")
    print(f"sig(hex, {len(sig_hex) // 2} bytes) = {sig_hex}")

    # Cross-validate with python's cryptography library.
    pub = RSAPublicNumbers(e=e, n=n).public_key()
    sig = bytes.fromhex(sig_hex)
    msg = bytes.fromhex(msg_hex)
    try:
        pub.verify(
            sig,
            msg,
            padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32),
            hashes.SHA256(),
        )
        print("cryptography.verify: VALID  (cross-check OK)")
    except InvalidSignature:
        print("cryptography.verify: INVALID — Wycheproof says valid but local crypto rejects; bug somewhere.")
        sys.exit(3)

    # Emit a Rust-friendly snippet for tests/rsa_pss_sha256_kat.rs.
    n_be_bytes = n.to_bytes(256, "big")
    print("\n---- Rust snippet ----")
    print(f"// Wycheproof rsa_pss_2048_sha256_mgf1_32 tcId {tc_id}: {comment!r}")
    print(f"let e: u32 = {e};")
    print(f"let n_hex = \"{n_be_bytes.hex()}\";  // 256 bytes big-endian")
    print(f"let msg_hex = \"{msg_hex}\";")
    print(f"let sig_hex = \"{sig_hex}\";")


if __name__ == "__main__":
    main()
