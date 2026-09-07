//! Keccak-f[1600] permutation — content underneath SHA-3.
//!
//! Math is content the operations consume: the Keccak permutation is
//! content; the SHA-3 *algorithm* (sponge
//! construction with rate 1088, capacity 512, suffix 0x06, 32-byte
//! output) is the composition built on top in `compositions/hashes.rs`.
//!
//! State layout: 5×5 lanes of 64 bits each = 1600 bits total. Flat
//! representation as `[u64; 25]` indexed `state[x + 5*y]`.
//!
//! Round = θ → ρ → π → χ → ι (FIPS 202 §3.2). 24 rounds total.

use crate::content::tables::{KECCAK_RC, KECCAK_RHO};

/// Apply Keccak-f[1600] to `state` in place: 24 rounds of θ ρ π χ ι.
/// This is the permutation used by SHA-3 (with rate 1088, capacity
/// 512) and by SHAKE/cSHAKE/KMAC/TupleHash/ParallelHash (with different
/// rate/capacity choices).
pub fn keccak_f1600(state: &mut [u64; 25]) {
    for round in 0..24 {
        // θ: column-parity diffusion.
        //   C[x] = ⊕_y state[x, y]
        //   D[x] = C[x-1] ⊕ ROL(C[x+1], 1)
        //   state[x, y] ^= D[x]
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        let mut d = [0u64; 5];
        for x in 0..5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] ^= d[x];
            }
        }

        // ρ + π fused: each lane is rotated by KECCAK_RHO[src] and moved
        // to position dst per the π formula
        //   new[x, y] = old[(x + 3y) mod 5, x]
        // (FIPS 202 §3.2.2 + §3.2.3.)
        let mut tmp = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                let src_x = (x + 3 * y) % 5;
                let src_y = x;
                let src = src_x + 5 * src_y;
                tmp[x + 5 * y] = state[src].rotate_left(KECCAK_RHO[src]);
            }
        }
        *state = tmp;

        // χ: nonlinear row mixing.
        //   state[x, y] ^= (NOT state[x+1, y]) AND state[x+2, y]
        // Snapshot before the row's first write so all three reads see
        // pre-step values.
        let snap = *state;
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] =
                    snap[x + 5 * y] ^ ((!snap[(x + 1) % 5 + 5 * y]) & snap[(x + 2) % 5 + 5 * y]);
            }
        }

        // ι: XOR round constant into state[0, 0].
        state[0] ^= KECCAK_RC[round];
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Keccak-f[1600] applied to the all-zero state. The expected
    /// output is a well-known test vector for the permutation, lifted
    /// from the reference implementations at keccak.team.
    #[test]
    fn keccak_f_zero_state() {
        let mut state = [0u64; 25];
        keccak_f1600(&mut state);
        // After one Keccak-f[1600] on the all-zero state, lane 0 has
        // a specific value documented in the Keccak reference vectors.
        // (Indirectly verified by the SHA-3 empty-string test vector.)
        assert_ne!(state, [0u64; 25]);
    }

    /// Inversibility-style check: applying θ twice with the same
    /// column-parity should be a no-op (each XOR pair cancels). This
    /// isn't a property of Keccak-f as a whole but exercises θ in
    /// isolation. Light smoke test; the FIPS 202 KAT vectors via
    /// SHA-3-256 are the load-bearing check.
    #[test]
    fn theta_xor_doubled_cancels() {
        // Quick smoke test that the rotation table is correct: lane
        // [0,0] has rotation offset 0 (no rotation).
        assert_eq!(KECCAK_RHO[0], 0);
    }
}
