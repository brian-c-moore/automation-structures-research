// Symmetric algorithms: instantiations of iterated_transformation and
// block_to_stream.
//
// AES-128 (ECB block) — iterated_transformation with 10-round AES.
// ChaCha20            — iterated_transformation with 20-round ARX, plus
//                       block_to_stream for encrypt.
// AES-128-CTR         — block_to_stream over AES-128.

pub mod aes128;
pub mod aes128_ctr;
pub mod chacha20;
