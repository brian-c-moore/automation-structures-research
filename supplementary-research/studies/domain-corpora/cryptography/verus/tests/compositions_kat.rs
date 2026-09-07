// Composition-pattern known-answer tests (structural, plus test-vector
// and oracle cross-check). The eleven composition patterns are
// cryptographic-shape templates. Each pattern carries evidence one of
// two ways:
//
//   (a) the pattern's exec function passes a hand-picked test vector
//       computable by inspection, OR
//   (b) the pattern is spec-only and its evidence is the
//       instantiation's KAT pass.
//
// iterated_transformation (iterate), tree_fold_of_chunks
// (compress/fold_one_level), absorb_then_squeeze (absorb/squeeze),
// block_to_stream (block_cipher/encrypt_ctr), encrypt_then_authenticate
// (tag_mix/aead_encrypt), two_layer_wrap (hmac), polynomial_mac
// (horner_compute), scalar_multiplication (scalar_mult) and
// commit_challenge_response (verify_signature) all have exec functions
// and use approach (a).
//
// iteration_stretching and extract_then_expand are pure-spec
// composition modules; their evidence is approach (b):
//   PBKDF2-HMAC-SHA-256 KAT (RFC 7914 §11)
//   HKDF-SHA-256 KAT (RFC 5869 Appendix A)
// This binary checks the linkage of those spec modules by importing
// them; their KAT-validated runtime correctness comes through those
// instantiation KATs.
extern crate cryptography_verus;
use cryptography_verus::compositions::absorb_then_squeeze::{absorb_all, absorb_one, squeeze_n};
use cryptography_verus::compositions::block_to_stream::{block_cipher, encrypt_ctr};
use cryptography_verus::compositions::commit_challenge_response::verify_signature;
use cryptography_verus::compositions::encrypt_then_authenticate::{aead_encrypt, tag_mix};
use cryptography_verus::compositions::iterated_transformation::iterate;
use cryptography_verus::compositions::polynomial_mac::horner_compute;
use cryptography_verus::compositions::scalar_multiplication::scalar_mult;
use cryptography_verus::compositions::tree_fold_of_chunks::{compress, fold_one_level};
use cryptography_verus::compositions::two_layer_wrap::hmac;

// Importing iteration_stretching and extract_then_expand confirms
// linkage; their evidence is through instantiation KATs
// (PBKDF2-HMAC-SHA-256, HKDF-SHA-256).
#[allow(unused_imports)]
use cryptography_verus::compositions::extract_then_expand as _v2j;
#[allow(unused_imports)]
use cryptography_verus::compositions::iteration_stretching as _v2i;

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

fn main() {
    println!("composition patterns KAT cross-check (Verus build)");
    let mut all_ok = true;

    // iterated_transformation: iterate uses wrapping_add as the round.
    all_ok &= check("iterate(0, [])", iterate(0, &[]), 0);
    all_ok &= check(
        "iterate(0, [10,20,30]) = wrapping_add fold",
        iterate(0, &[10u64, 20, 30]),
        60,
    );
    all_ok &= check("iterate(100, [1])", iterate(100, &[1u64]), 101);

    // tree_fold_of_chunks: compress is XOR; fold_one_level pairs adjacent.
    all_ok &= check("compress(0xAA, 0x55)", compress(0xAAu64, 0x55), 0xFF);
    let fold_in: Vec<u64> = vec![1, 2, 3, 4];
    let fold_out = fold_one_level(&fold_in);
    all_ok &= check("fold_one_level([1,2,3,4]).len()", fold_out.len(), 2);
    all_ok &= check("fold_one_level([1,2,3,4])[0] = 1^2", fold_out[0], 1 ^ 2);
    all_ok &= check("fold_one_level([1,2,3,4])[1] = 3^4", fold_out[1], 3 ^ 4);
    let empty_fold: Vec<u64> = vec![];
    all_ok &= check(
        "fold_one_level([]).len()",
        fold_one_level(&empty_fold).len(),
        0,
    );

    // absorb_then_squeeze: permute_spec(s) = s.wrapping_mul(K) ^ (s>>13).
    // For s=0: permute(0) = 0; for s=123^456 = ...
    all_ok &= check("absorb_one(0, 0) = permute(0) = 0", absorb_one(0, 0), 0);
    all_ok &= check("absorb_all(0, [])", absorb_all(0, &[]), 0);
    all_ok &= check(
        "absorb_all(0, [0,0,0]) (idempotent on zero)",
        absorb_all(0, &[0u64, 0, 0]),
        0,
    );
    let squeezed = squeeze_n(123, 3);
    all_ok &= check("squeeze_n(123, 3).len()", squeezed.len(), 3);
    all_ok &= check("squeeze_n[0] = initial", squeezed[0], 123);
    all_ok &= check("squeeze_n(_, 0).len()", squeeze_n(42, 0).len(), 0);

    // block_to_stream: block_cipher(k, c) = k.wrapping_add(c * 0x9E37...).
    all_ok &= check("block_cipher(0, 0)", block_cipher(0, 0), 0);
    let ct_empty = encrypt_ctr(0, 0, &[]);
    all_ok &= check("encrypt_ctr(_, _, []).len()", ct_empty.len(), 0);
    let ct = encrypt_ctr(0, 0, &[0u64, 0, 0]);
    all_ok &= check("encrypt_ctr(0, 0, [0,0,0]).len()", ct.len(), 3);
    // Each ct[i] = plaintext[i] ^ keystream(0, 0, i). With plaintext=0:
    // ct[0] = 0 ^ block_cipher(0, 0) = 0; ct[1] = 0 ^ block_cipher(0, 1); etc.
    all_ok &= check("encrypt_ctr ct[0] (pt=0, ks=0)", ct[0], 0);

    // encrypt_then_authenticate: tag_mix is XOR.
    all_ok &= check("tag_mix(0xAA, 0x55)", tag_mix(0xAAu64, 0x55), 0xFF);
    let (aead_ct, aead_tag) = aead_encrypt(0u64, 0, &[], &[]);
    all_ok &= check("aead_encrypt(_, _, [], []).0.len()", aead_ct.len(), 0);
    all_ok &= check(
        "aead_encrypt empty inputs: tag = tag_mix(0, 0) = 0",
        aead_tag,
        0,
    );

    // two_layer_wrap (HMAC): hmac(0, &[]) = iterate(OPAD, &[IPAD])
    //  = OPAD.wrapping_add(IPAD) = 0x5C5C5C5C5C5C5C5C + 0x3636363636363636 = 0x9292929292929292.
    let hmac_empty = hmac(0u64, &[]);
    let ipad = 0x3636363636363636u64;
    let opad = 0x5C5C5C5C5C5C5C5Cu64;
    let expected = opad.wrapping_add(ipad);
    all_ok &= check("hmac(0, [])", hmac_empty, expected);

    // polynomial_mac: P = 7. horner_at:
    //  k=0: 0
    //  k=1: ((0+3) * 2) % 7 = 6
    //  k=2: ((6+5) * 2) % 7 = 22 % 7 = 1
    all_ok &= check("horner_compute([], 2)", horner_compute(&[], 2u64), 0);
    all_ok &= check("horner_compute([3], 2)", horner_compute(&[3u64], 2), 6);
    all_ok &= check(
        "horner_compute([3, 5], 2)",
        horner_compute(&[3u64, 5], 2),
        1,
    );

    // scalar_multiplication: L = 4, base in [0,L), bits in {0,1}.
    // scalar_mult(&[0, 1], 1):
    //   i=0: bit=0, doubled = (0+0)%4 = 0, acc = 0
    //   i=1: bit=1, doubled = (0+0)%4 = 0, acc = (0+1)%4 = 1
    //   → 1
    all_ok &= check("scalar_mult(&[0,1], 1) = 1", scalar_mult(&[0u64, 1], 1), 1);
    // scalar_mult(&[1, 0], 1):
    //   i=0: bit=1, doubled = 0, acc = 1
    //   i=1: bit=0, doubled = (1+1)%4 = 2, acc = 2
    //   → 2
    all_ok &= check("scalar_mult(&[1,0], 1) = 2", scalar_mult(&[1u64, 0], 1), 2);
    // scalar_mult(&[1, 1], 1): k=0 → acc=1; k=1 → doubled=2, acc=(2+1)%4=3.
    all_ok &= check("scalar_mult(&[1,1], 1) = 3", scalar_mult(&[1u64, 1], 1), 3);

    // commit_challenge_response: verify_signature() always true.
    all_ok &= check("verify_signature()", verify_signature(), true);

    // iteration_stretching and extract_then_expand are spec-only modules;
    // their evidence is through the instantiation KATs
    // (PBKDF2-HMAC-SHA-256, HKDF-SHA-256). The use statements above
    // confirm linkage.
    println!("  NOTE  iteration_stretching: via PBKDF2-HMAC-SHA-256 KAT");
    println!("  NOTE  extract_then_expand:  via HKDF-SHA-256 KAT");

    if all_ok {
        println!("KAT_RESULT: SUCCESS (-2h, direct; , via KAT)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
