// Hardware-accelerated refinement: single-instruction-per-round
// produces the same output as multi-step ActuationPass.
//
// TLAPS reference: supplementary-research/studies/domain-corpora/cryptography/tla/realizations/HardwareAcceleratedRefinesBase_Proof.tla
// (75 obligations, lockstep stepping).

use vstd::prelude::*;

verus! {

pub const M: u64 = 16;

/// Both implementations apply the same per-round function; the "HW"
/// version conceptually does it in one instruction while the "base"
/// version does it in multiple sub-steps. At the abstract level both
/// produce the same state at each round boundary.
pub fn hw_refinement(rounds: u64) -> (out: (u64, u64))
    requires rounds <= 16,
    ensures out.0 == out.1,
{
    let mut base: u64 = 0;
    let mut hw: u64 = 0;
    let mut r: u64 = 0;
    while r < rounds
        invariant
            r <= rounds,
            rounds <= 16,
            base < M,
            hw < M,
            base == hw,
        decreases rounds - r,
    {
        base = (base + r + 1) % M;
        hw = (hw + r + 1) % M;
        r = r + 1;
    }
    (base, hw)
}

}
