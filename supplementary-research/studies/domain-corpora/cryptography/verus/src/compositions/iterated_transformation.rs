// IteratedTransformationOverChainedState.
//
// The dominant cryptographic composition pattern:
// a fixed state is iteratively transformed by a round function applied
// to successive inputs. Twelve of the fifteen corpus algorithms
// instantiate this pattern (SHA-256, SHA-3 round structure, AES rounds,
// ChaCha20 rounds, HMAC nested hashing, HKDF expansion, PBKDF2, RSA
// modular exponentiation, Ed25519 scalar mult, X25519 ladder).
//
// The TLA+ spec at supplementary-research/studies/domain-corpora/cryptography/tla/compositions/
// IteratedTransformationOverChainedState.tla proves four invariants:
//
//   TypeInvariant         (state, i, history typing)
//   HistoryStartsAtInit   (history[1] = InitialState)
//   ChainedStateCorrect   (state = history[Len(history)])
//   HistoryConsistent     (history[k+1] = RoundFn(history[k], inputs[k]))
//
// The TLAPS proof is 156 obligations cold-deterministic. Its
// representation is sequence-history plus index-based reasoning, which
// avoids recursive function-fixpoint operators.
//
// The Verus translation here exploits Verus's native recursive-spec-fn
// support (a structural difference from TLAPS): the spec function
// `iterate_spec(init, inputs, n)` is recursive with `decreases n` and
// closes natively. The four TLAPS invariants collapse to a single
// ensures clause: `result == iterate_spec(initial, inputs@, len)`.
//
// RoundFn instantiation. The TLA+ spec uses an uninterpreted RoundFn
// (defined as an IF-THEN-ELSE table); the Verus structural-verification
// layer uses the concrete additive round (a + b) mod 2^64 as a
// representative AC operator. Specific cryptographic round
// functions (SHA-256's Σ-Ch-Maj, ChaCha20's quarter-round, etc.)
// instantiate the same pattern with different operators and are
// verified per-algorithm in the algorithm modules.
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

/// The round function: combines the running state with the current
/// input. Concrete AC operator (wrapping add) for the structural
/// verification; per-algorithm round functions instantiate this in the
/// algorithm modules.
pub open spec fn round_spec(state: u64, input: u64) -> u64 {
    state.wrapping_add(input)
}

pub fn round(state: u64, input: u64) -> (r: u64)
    ensures r == round_spec(state, input),
{
    state.wrapping_add(input)
}

/// Mathematical iterate: apply the round function `n` times over the
/// first `n` elements of `inputs`, starting from `initial`. Recursive
/// spec function; `decreases n` witnesses termination.
pub open spec fn iterate_spec(initial: u64, inputs: Seq<u64>, n: int) -> u64
    decreases n,
{
    if n <= 0 {
        initial
    } else if n > inputs.len() as int {
        initial
    } else {
        round_spec(iterate_spec(initial, inputs, n - 1), inputs[n - 1])
    }
}

/// Executable iterate: imperative loop applying the round function
/// for each input in order. The loop invariant captures HistoryConsistent
/// (the running state at iteration `i` equals iterate_spec(initial,
/// inputs@, i)).
///
/// The TLAPS proof's four-invariant conjunction (TypeInvariant,
/// HistoryStartsAtInit, ChainedStateCorrect, HistoryConsistent)
/// collapses into the single ensures clause here because Verus's
/// recursive spec function captures the chain semantics directly.
pub fn iterate(initial: u64, inputs: &[u64]) -> (result: u64)
    ensures
        result == iterate_spec(initial, inputs@, inputs@.len() as int),
{
    let n: usize = inputs.len();
    let mut state: u64 = initial;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == inputs@.len(),
            state == iterate_spec(initial, inputs@, i as int),
        decreases n - i,
    {
        state = round(state, inputs[i]);
        i = i + 1;
    }
    state
}

}
