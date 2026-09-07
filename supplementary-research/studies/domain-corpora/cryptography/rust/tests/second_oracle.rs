//! Second-oracle comparison against independent Rust cryptography crates
//! rather than the local Python bridge.
//!
//! Each test compares the six-primitive composition against the
//! corresponding RustCrypto crate on a deterministic set of random
//! inputs. Three-way triangulation across (vendored KAT vectors,
//! Python `pyca/cryptography`, RustCrypto crate) makes any disagreement
//! a finding worth recording.
//!
//! Mirrors the execution-structure study's `direct_comparison/` pattern:
//! each second-oracle test is gated by the corresponding RustCrypto crate being in the
//! dev-dependency graph. The checked-in graph covers the exact seven
//! algorithms registered by this crate.

use dac_cryptography::compositions::hashes::{blake3_hash, sha256, sha3_256};
use dac_cryptography::primitives::Sampler;

/// Shared comparison loop: 200 deterministic random byte messages of
/// length 0..=512, compared byte-exact against the RustCrypto crate
/// supplied as the reference closure.
fn cross_check<F, G>(ours_fn: F, theirs_fn: G, name: &str)
where
    F: Fn(&[u8]) -> Vec<u8>,
    G: Fn(&[u8]) -> Vec<u8>,
{
    let mut s = Sampler::new(0xC0FFEE);
    let mut mismatches = Vec::new();

    for i in 0..200 {
        let len = s.pick_index(513);
        let msg = s.bytes(len);

        let ours = ours_fn(&msg);
        let theirs = theirs_fn(&msg);

        if ours != theirs {
            mismatches.push((i, len, msg.clone(), ours, theirs));
            if mismatches.len() >= 5 {
                break;
            }
        }
    }

    if !mismatches.is_empty() {
        for (i, len, msg, ours, theirs) in &mismatches {
            eprintln!(
                "{name} DIVERGENCE at iter={i} len={len}\n  msg[..min]:  {:02x?}\n  ours:    {:02x?}\n  theirs:  {:02x?}",
                &msg[..msg.len().min(16)],
                ours,
                theirs
            );
        }
        panic!(
            "{name} composition disagrees with the RustCrypto reference on {} of 200 inputs",
            mismatches.len()
        );
    }
}

/// SHA-256 vs. RustCrypto `sha2` crate.
#[test]
fn sha256_matches_sha2_crate() {
    use sha2::{Digest, Sha256};
    cross_check(
        |msg| sha256(msg).to_vec(),
        |msg| {
            let mut h = Sha256::new();
            h.update(msg);
            h.finalize().to_vec()
        },
        "sha256",
    );
}

/// SHA-3-256 vs. RustCrypto `sha3` crate.
#[test]
fn sha3_256_matches_sha3_crate() {
    use sha3::{Digest, Sha3_256};
    cross_check(
        |msg| sha3_256(msg).to_vec(),
        |msg| {
            let mut h = Sha3_256::new();
            h.update(msg);
            h.finalize().to_vec()
        },
        "sha3_256",
    );
}

/// BLAKE3 vs. RustCrypto `blake3` crate.
#[test]
fn blake3_matches_blake3_crate() {
    cross_check(
        |msg| blake3_hash(msg).to_vec(),
        |msg| blake3::hash(msg).as_bytes().to_vec(),
        "blake3",
    );
}

/// ChaCha20 encrypt vs. RustCrypto `chacha20` crate, on 200 random
/// (key, nonce, counter, plaintext) tuples. The RustCrypto crate's
/// `ChaCha20` cipher uses an [`NewCipher`]-style API; for ChaCha20 the
/// nonce is 12 bytes and `seek()` selects the starting block counter.
#[test]
fn chacha20_matches_chacha20_crate() {
    use chacha20::cipher::{KeyIvInit, StreamCipher, StreamCipherSeek};
    use chacha20::ChaCha20;
    use dac_cryptography::compositions::symmetric::chacha20_encrypt;

    let mut s = Sampler::new(0xC0DEBA5E);
    let mut mismatches = Vec::new();

    for i in 0..200 {
        let key_bytes = s.bytes(32);
        let nonce_bytes = s.bytes(12);
        let counter = (s.pick_index(1024)) as u32;
        let plen = s.pick_index(257);
        let plaintext = s.bytes(plen);

        let mut key = [0u8; 32];
        key.copy_from_slice(&key_bytes);
        let mut nonce = [0u8; 12];
        nonce.copy_from_slice(&nonce_bytes);

        let ours = chacha20_encrypt(&key, counter, &nonce, &plaintext);

        // RustCrypto chacha20: build a cipher with the 12-byte nonce,
        // seek to the right byte position (counter × 64), then encrypt.
        let mut cipher = ChaCha20::new(&key.into(), &nonce.into());
        cipher.seek((counter as u64) * 64);
        let mut theirs = plaintext.clone();
        cipher.apply_keystream(&mut theirs);

        if ours != theirs {
            mismatches.push((i, plen, counter, ours, theirs));
            if mismatches.len() >= 5 {
                break;
            }
        }
    }

    if !mismatches.is_empty() {
        for (i, plen, counter, ours, theirs) in &mismatches {
            eprintln!(
                "chacha20 DIVERGENCE at iter={i} plen={plen} counter={counter}\n  ours[..min]:    {:02x?}\n  theirs[..min]:  {:02x?}",
                &ours[..ours.len().min(16)],
                &theirs[..theirs.len().min(16)],
            );
        }
        panic!(
            "chacha20 composition disagrees with chacha20 crate on {} of 200 inputs",
            mismatches.len()
        );
    }
}

/// HMAC-SHA-256 vs. RustCrypto `hmac` + `sha2` crates.
#[test]
fn hmac_sha256_matches_hmac_crate() {
    use dac_cryptography::compositions::mac::hmac_sha256;
    use hmac::{Hmac, Mac};
    use sha2::Sha256;

    type HmacSha256 = Hmac<Sha256>;

    let mut s = Sampler::new(0xBADF00D);
    let mut mismatches = Vec::new();

    for i in 0..200 {
        let klen = s.pick_index(200);
        let mlen = s.pick_index(257);
        let key = s.bytes(klen);
        let msg = s.bytes(mlen);

        let ours = hmac_sha256(&key, &msg).to_vec();

        let mut mac = HmacSha256::new_from_slice(&key).unwrap();
        mac.update(&msg);
        let theirs = mac.finalize().into_bytes().to_vec();

        if ours != theirs {
            mismatches.push((i, klen, mlen, ours, theirs));
            if mismatches.len() >= 5 {
                break;
            }
        }
    }

    if !mismatches.is_empty() {
        for (i, klen, mlen, ours, theirs) in &mismatches {
            eprintln!(
                "hmac_sha256 DIVERGENCE at iter={i} klen={klen} mlen={mlen}\n  ours:    {:02x?}\n  theirs:  {:02x?}",
                ours, theirs
            );
        }
        panic!(
            "hmac_sha256 composition disagrees with hmac crate on {} of 200 inputs",
            mismatches.len()
        );
    }
}

/// HKDF-SHA-256 vs. RustCrypto `hkdf` + `sha2` crates.
#[test]
fn hkdf_sha256_matches_hkdf_crate() {
    use dac_cryptography::compositions::kdf::hkdf_sha256;
    use hkdf::Hkdf;
    use sha2::Sha256;

    let mut s = Sampler::new(0xCABBA9E);
    let mut mismatches = Vec::new();

    for i in 0..200 {
        let saltlen = s.pick_index(64);
        let ikmlen = 1 + s.pick_index(80);
        let infolen = s.pick_index(64);
        let length = 1 + s.pick_index(200);

        let salt = s.bytes(saltlen);
        let ikm = s.bytes(ikmlen);
        let info = s.bytes(infolen);

        let ours = hkdf_sha256(&salt, &ikm, &info, length);

        let hk = Hkdf::<Sha256>::new(if salt.is_empty() { None } else { Some(&salt) }, &ikm);
        let mut theirs = vec![0u8; length];
        hk.expand(&info, &mut theirs).expect("hkdf expand");

        if ours != theirs {
            mismatches.push((i, saltlen, ikmlen, infolen, length, ours, theirs));
            if mismatches.len() >= 5 {
                break;
            }
        }
    }

    if !mismatches.is_empty() {
        for (i, sl, il, fl, ll, ours, theirs) in &mismatches {
            eprintln!(
                "hkdf_sha256 DIVERGENCE at iter={i} salt={sl} ikm={il} info={fl} len={ll}\n  ours:    {:02x?}\n  theirs:  {:02x?}",
                ours, theirs
            );
        }
        panic!(
            "hkdf_sha256 composition disagrees with hkdf crate on {} of 200 inputs",
            mismatches.len()
        );
    }
}

/// PBKDF2-HMAC-SHA-256 vs. RustCrypto `pbkdf2` + `sha2` crates.
/// Iteration count is kept small (1..16) so the test runs fast.
#[test]
fn pbkdf2_hmac_sha256_matches_pbkdf2_crate() {
    use dac_cryptography::compositions::kdf::pbkdf2_hmac_sha256;
    use pbkdf2::pbkdf2_hmac;
    use sha2::Sha256;

    let mut s = Sampler::new(0xFEED1979);
    let mut mismatches = Vec::new();

    for i in 0..100 {
        let pwd_len = s.pick_index(40);
        let salt_len = s.pick_index(40);
        let iterations = 1u32 + (s.pick_index(16) as u32);
        let length = 1 + s.pick_index(80);

        let pwd = s.bytes(pwd_len);
        let salt = s.bytes(salt_len);

        let ours = pbkdf2_hmac_sha256(&pwd, &salt, iterations, length);

        let mut theirs = vec![0u8; length];
        pbkdf2_hmac::<Sha256>(&pwd, &salt, iterations, &mut theirs);

        if ours != theirs {
            mismatches.push((i, pwd_len, salt_len, iterations, length, ours, theirs));
            if mismatches.len() >= 5 {
                break;
            }
        }
    }

    if !mismatches.is_empty() {
        for (i, pl, sl, c, ll, ours, theirs) in &mismatches {
            eprintln!(
                "pbkdf2 DIVERGENCE at iter={i} pwd={pl} salt={sl} c={c} len={ll}\n  ours:    {:02x?}\n  theirs:  {:02x?}",
                ours, theirs
            );
        }
        panic!(
            "pbkdf2_hmac_sha256 composition disagrees with pbkdf2 crate on {} of 100 inputs",
            mismatches.len()
        );
    }
}
