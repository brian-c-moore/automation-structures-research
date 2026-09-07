#!/usr/bin/env python3
# ed25519 Python reference implementation per RFC 8032 §5.1.5.
# Used as a side-by-side debug oracle for the Verus implementation.
# Single-purpose: dump intermediate values for RFC 8032 §7.1 Test 1 and Test 2.

import hashlib

# Field arithmetic mod p = 2^255 - 19
P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493  # group order
D = -121665 * pow(121666, P - 2, P) % P              # curve constant
I = pow(2, (P - 1) // 4, P)                          # sqrt(-1)

def modp_inv(x):
    return pow(x, P - 2, P)

def recover_x(y, sign):
    if y >= P:
        return None
    x2 = (y * y - 1) * modp_inv(D * y * y + 1) % P
    if x2 == 0:
        if sign:
            return None
        return 0
    x = pow(x2, (P + 3) // 8, P)
    if (x * x - x2) % P != 0:
        x = x * I % P
    if (x * x - x2) % P != 0:
        return None
    if (x & 1) != sign:
        x = P - x
    return x

# Basepoint
G_Y = 4 * modp_inv(5) % P
G_X = recover_x(G_Y, 0)
G = (G_X, G_Y, 1, G_X * G_Y % P)

def point_add(P_, Q_):
    A_ = (P_[1] - P_[0]) * (Q_[1] - Q_[0]) % P
    B_ = (P_[1] + P_[0]) * (Q_[1] + Q_[0]) % P
    C_ = 2 * P_[3] * Q_[3] * D % P
    D_ = 2 * P_[2] * Q_[2] % P
    E_, F_, G2, H2 = B_ - A_, D_ - C_, D_ + C_, B_ + A_
    return (E_ * F_ % P, G2 * H2 % P, F_ * G2 % P, E_ * H2 % P)

def point_mul(s, P_):
    Q = (0, 1, 1, 0)
    while s > 0:
        if s & 1:
            Q = point_add(Q, P_)
        P_ = point_add(P_, P_)
        s >>= 1
    return Q

def point_compress(P_):
    zinv = modp_inv(P_[2])
    x = P_[0] * zinv % P
    y = P_[1] * zinv % P
    return int.to_bytes(y | ((x & 1) << 255), 32, "little")

def point_decompress(s):
    if len(s) != 32:
        raise Exception("Invalid input length for decompression")
    y = int.from_bytes(s, "little")
    sign = y >> 255
    y &= (1 << 255) - 1
    x = recover_x(y, sign)
    if x is None:
        return None
    return (x, y, 1, x * y % P)

def sha512(s):
    return hashlib.sha512(s).digest()

def sha512_modq(s):
    return int.from_bytes(sha512(s), "little") % L

def verify_dump(public_key_hex, message, signature_hex, label):
    print(f"=== {label} ===")
    A = bytes.fromhex(public_key_hex)
    sig = bytes.fromhex(signature_hex)
    R_bytes = sig[:32]
    S_bytes = sig[32:]
    print(f"A = {A.hex()}")
    print(f"R = {R_bytes.hex()}")
    print(f"S = {S_bytes.hex()}")
    print(f"M = {message.hex() if message else '(empty)'}")

    h_input = R_bytes + A + message
    h_full = sha512(h_input)
    print(f"H = SHA-512(R || A || M) = {h_full.hex()}")

    k_int = int.from_bytes(h_full, "little")
    print(f"k_int (raw, hex) = {hex(k_int)}")
    k_red = k_int % L
    print(f"k_red = k_int mod L (hex) = {hex(k_red)}")
    k_red_bytes = int.to_bytes(k_red, 32, "little")
    print(f"k_red_bytes (LE) = {k_red_bytes.hex()}")

    pt_A = point_decompress(A)
    if pt_A is None:
        print("decompress(A) FAILED")
        return False
    print(f"decompress(A): X = {hex(pt_A[0])}")
    print(f"               Y = {hex(pt_A[1])}")
    print(f"               Z = {hex(pt_A[2])}")
    print(f"               T = {hex(pt_A[3])}")

    pt_R = point_decompress(R_bytes)
    if pt_R is None:
        print("decompress(R) FAILED")
        return False
    print(f"decompress(R): X = {hex(pt_R[0])}")
    print(f"               Y = {hex(pt_R[1])}")
    print(f"               Z = {hex(pt_R[2])}")
    print(f"               T = {hex(pt_R[3])}")

    s_int = int.from_bytes(S_bytes, "little")
    if s_int >= L:
        print("S >= L, signature INVALID")
        return False
    print(f"S as int (hex) = {hex(s_int)}")

    sB = point_mul(s_int, G)
    print(f"sB:  X = {hex(sB[0])}")
    print(f"     Y = {hex(sB[1])}")
    print(f"     Z = {hex(sB[2])}")

    kA = point_mul(k_red, pt_A)
    print(f"kA:  X = {hex(kA[0])}")
    print(f"     Y = {hex(kA[1])}")
    print(f"     Z = {hex(kA[2])}")

    R_plus_kA = point_add(pt_R, kA)
    print(f"R+kA: X = {hex(R_plus_kA[0])}")
    print(f"      Y = {hex(R_plus_kA[1])}")
    print(f"      Z = {hex(R_plus_kA[2])}")

    # Compare sB == R + kA in projective: x_lhs * z_rhs == x_rhs * z_lhs
    eq_x = (sB[0] * R_plus_kA[2] - R_plus_kA[0] * sB[2]) % P == 0
    eq_y = (sB[1] * R_plus_kA[2] - R_plus_kA[1] * sB[2]) % P == 0
    print(f"points_equal = {eq_x and eq_y} (x={eq_x}, y={eq_y})")
    return eq_x and eq_y


verify_dump(
    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
    b"",
    "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
    "RFC 8032 §7.1 Test 1 (empty)",
)

print()

verify_dump(
    "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
    bytes([0x72]),
    "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
    "RFC 8032 §7.1 Test 2 (1-byte 0x72)",
)
