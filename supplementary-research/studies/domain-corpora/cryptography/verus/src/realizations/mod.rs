// Implementation-realization refinement specifications.
//
// Three refinement modules verifying that each realization produces
// the same output as the base iterated-transformation:
//   bitsliced            — N inputs in parallel via packed register
//                          (mirrors TLAPS BitslicedRefinesBase,
//                          88 obligations)
//   hardware_accelerated — single-instruction-per-round vs multi-step
//                          (mirrors TLAPS HardwareAcceleratedRefinesBase,
//                          75 obligations)
//   simd_lane_batched    — N SIMD lanes parallel to sequential invocations
//                          (mirrors TLAPS SimdLaneBatchedRefinesBase,
//                          89 obligations)
//
// Under lockstep stepping, each realization advances in lockstep with
// the base composition on a shared index; the refinement invariant is
// unconditional and inductive by construction.

pub mod bitsliced;
pub mod hardware_accelerated;
pub mod simd_lane_batched;
pub mod bitsliced_aes;
pub mod bitsliced_keccak;
pub mod pclmulqdq;
pub mod sha_ni;
pub mod simd_aes_ctr;
pub mod simd_poly1305;
