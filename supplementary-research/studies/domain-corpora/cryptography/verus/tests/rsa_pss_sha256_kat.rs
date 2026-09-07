// RSA-PSS-SHA-256 (PKCS#1 v2.2, RFC 8017) known-answer-test (verify only).
//
// Two independent vectors:
//   1. Wycheproof rsa_pss_2048_sha256_mgf1_32 tcId 1 ("valid signature")
//      Source: https://github.com/C2SP/wycheproof
//              testvectors_v1/rsa_pss_2048_sha256_mgf1_32_test.json
//      e = 65537, msg = empty, salt_length = 32.
//   2. NIST CAVP FIPS 186-3 SigVerPSS_186-3.rsp first 2048+SHA-256 vector
//      with Result = P. e = 0x10e43f, salt_length = 32.
//
// Both vectors were cross-validated with python cryptography (OpenSSL
// backend) prior to embedding so the KAT does not trust any single
// source.
extern crate cryptography_verus;
use cryptography_verus::algorithms::asymmetric::rsa_pss_sha256::rsa_pss_sha256_verify;

fn from_hex(s: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len() / 2);
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let hi = match bytes[i] {
            b'0'..=b'9' => bytes[i] - b'0',
            b'a'..=b'f' => bytes[i] - b'a' + 10,
            b'A'..=b'F' => bytes[i] - b'A' + 10,
            _ => 0,
        };
        let lo = match bytes[i + 1] {
            b'0'..=b'9' => bytes[i + 1] - b'0',
            b'a'..=b'f' => bytes[i + 1] - b'a' + 10,
            b'A'..=b'F' => bytes[i + 1] - b'A' + 10,
            _ => 0,
        };
        out.push((hi << 4) | lo);
        i += 2;
    }
    out
}

fn to_arr256(v: &[u8]) -> [u8; 256] {
    let mut a = [0u8; 256];
    for i in 0..256 {
        a[i] = v[i];
    }
    a
}

fn check_pass(name: &str, n_hex: &str, e: u32, msg: &[u8], sig_hex: &str) -> bool {
    let n = to_arr256(&from_hex(n_hex));
    let sig = to_arr256(&from_hex(sig_hex));
    let ok = rsa_pss_sha256_verify(&n, e, msg, &sig, 32);
    if ok {
        println!("  PASS  {}", name);
    } else {
        println!("  FAIL  {} (expected valid, verify returned false)", name);
    }
    ok
}

fn main() {
    println!("PKCS#1 v2.2 RSA-PSS-SHA-256 KAT cross-check (Verus build)");
    let mut all_ok = true;

    // Vector 1: Wycheproof rsa_pss_2048_sha256_mgf1_32 tcId 1
    all_ok &= check_pass(
        "Wycheproof rsa_pss_2048_sha256_mgf1_32 tcId 1 (empty message)",
        "a2b451a07d0aa5f96e455671513550514a8a5b462ebef717094fa1fee82224e637f9746d3f7cafd31878d80325b6ef5a1700f65903b469429e89d6eac8845097b5ab393189db92512ed8a7711a1253facd20f79c15e8247f3d3e42e46e48c98e254a2fe9765313a03eff8f17e1a029397a1fa26a8dce26f490ed81299615d9814c22da610428e09c7d9658594266f5c021d0fceca08d945a12be82de4d1ece6b4c03145b5d3495d4ed5411eb878daf05fd7afc3e09ada0f1126422f590975a1969816f48698bcbba1b4d9cae79d460d8f9f85e7975005d9bc22c4e5ac0f7c1a45d12569a62807d3b9a02e5a530e773066f453d1f5b4c2e9cf7820283f742b9d5",
        65537,
        b"",
        "4f01e0c12b08625ecac89a69231906edf826380f37c959a96690d046316d68ffce9d5c471694fcebfc6b45534864689256e4fc81c78e583f675d0c94b449647451e81beff01a11a516d5e5ce3f1a910437cb8a3a5096b19fb15f4524a35b23d89cdba12cf5b71aac1047b28c562df7c5542c34ce23a182cf7e0e231934b17294799d44877a1d68ef1b8f073619b7618e6b7c22db20030d98cf591ffc3d4da5f58613ecd5ecfc3b40a1d02f40891ca43695cd4c088b05a8054c89c595a47e274816f35384226f74459ee63e25a1bfc03c360490552ec38343f8ace502f065303b00bc0ec320711b211fde92e57feb9013c3609342495ec0d7cabdec21e54acc38",
    );

    // Vector 2: NIST CAVP FIPS 186-3 SigVerPSS first SHA-256/Result=P vector
    let v2_msg = from_hex("e002377affb04f0fe4598de9d92d31d6c786040d5776976556a2cfc55e54a1dcb3cb1b126bd6a4bed2a184990ccea773fcc79d246553e6c64f686d21ad4152673cafec22aeb40f6a084e8a5b4991f4c64cf8a927effd0fd775e71e8329e41fdd4457b3911173187b4f09a817d79ea2397fc12dfe3d9c9a0290c8ead31b6690a6");
    all_ok &= check_pass(
        "NIST CAVP FIPS 186-3 SigVerPSS first SHA-256 Result=P vector",
        "a47d04e7cacdba4ea26eca8a4c6e14563c2ce03b623b768c0d49868a57121301dbf783d82f4c055e73960e70550187d0af62ac3496f0a3d9103c2eb7919a72752fa7ce8c688d81e3aee99468887a15288afbb7acb845b7c522b5c64e678fcd3d22feb84b44272700be527d2b2025a3f83c2383bf6a39cf5b4e48b3cf2f56eef0dfff18555e31037b915248694876f3047814415164f2c660881e694b58c28038a032ad25634aad7b39171dee368e3d59bfb7299e4601d4587e68caaf8db457b75af42fc0cf1ae7caced286d77fac6cedb03ad94f1433d2c94d08e60bc1fdef0543cd2951e765b38230fdd18de5d2ca627ddc032fe05bbd2ff21e2db1c2f94d8b",
        0x10e43f,
        &v2_msg,
        "4f9b425c2058460e4ab2f5c96384da2327fd29150f01955a76b4efe956af06dc08779a374ee4607eab61a93adc5608f4ec36e47f2a0f754e8ff839a8a19b1db1e884ea4cf348cd455069eb87afd53645b44e28a0a56808f5031da5ba9112768dfbfca44ebe63a0c0572b731d66122fb71609be1480faa4e4f75e43955159d70f081e2a32fbb19a48b9f162cf6b2fb445d2d6994bc58910a26b5943477803cdaaa1bd74b0da0a5d053d8b1dc593091db5388383c26079f344e2aea600d0e324164b450f7b9b465111b7265f3b1b063089ae7e2623fc0fda8052cf4bf3379102fbf71d7c98e8258664ceed637d20f95ff0111881e650ce61f251d9c3a629ef222d",
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (2/2)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
