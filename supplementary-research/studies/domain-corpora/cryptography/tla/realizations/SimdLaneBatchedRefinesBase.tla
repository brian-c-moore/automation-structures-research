---- MODULE SimdLaneBatchedRefinesBase ----
(*
  SIMD-lane-batched realization refines the base
  iterated-transformation composition (refinement of
  IteratedTransformationOverChainedState).

  Models N inputs flowing through the same iterated-transformation
  state machine, in two parallel implementations:
    Base — N independent sequential invocations (one per input). Each
      invocation runs RoundFn(state, round) at every round.
    SIMD — N lanes batched in a single SIMD register; per round one
      SIMD instruction updates all N lanes simultaneously. Per-lane
      reads are independent of other lanes (no inter-lane dependency).

  Refinement mapping: extract lane k from the SIMD state for each k.
  For every k, base_states[k] = simd_state[k]. The refinement holds
  by construction: both apply the same RoundFn componentwise. The
  SIMD realization is a composition choice within the build; it is
  not a build-requirement change.

  Mirrors BitslicedRefinesBase's lockstep refinement pattern. Where that
  module models bit-level parallelism (bits of N inputs across a register's
  bit-positions), this one models lane-level parallelism (whole values across
  N lanes). The TLA+-level structure is the same; the two differ only in the
  realization mechanism they stand for.

  Modeled instantiation: ChaCha20 4-block SIMD batch.
  Bounded parameters per the study definition: N = 4 lanes, 2 blocks per
  lane (we model the per-block count as `Rounds` here for clarity).
  The theorem is limited to N = 4, Rounds = 2, and Bits = 4 in this
  abstract lockstep model; it does not establish concrete ChaCha20 semantics.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    N,         \* number of SIMD lanes
    Rounds,    \* per-lane block count (number of rounds)
    Bits       \* per-state bit width

ASSUME NType      == N \in Nat /\ N >= 1 /\ N <= 4
ASSUME RoundsType == Rounds \in Nat /\ Rounds >= 1 /\ Rounds <= 4
ASSUME BitsType   == Bits \in Nat /\ Bits >= 1 /\ Bits <= 4
ASSUME NConcrete      == N = 4
ASSUME RoundsConcrete == Rounds = 2
ASSUME BitsConcrete   == Bits = 4

M == 2 ^ Bits
ASSUME MConcrete == M = 16
StateValue == 0..(M - 1)
LaneIdx == 0..(N - 1)

\* Per-round transformation (per-lane).
RoundFn(s, r) == (s + r) % M

\* Initial state per lane. Lane k starts at value k mod M.
Init0(k) == k % M

VARIABLES
    base_states,         \* [LaneIdx -> StateValue] - sequential per-lane state
    simd_state,          \* [LaneIdx -> StateValue] - SIMD-batched state
    rnd                  \* shared round counter 0..Rounds

vars == <<base_states, simd_state, rnd>>

TypeInvariant ==
    /\ base_states \in [LaneIdx -> StateValue]
    /\ simd_state \in [LaneIdx -> StateValue]
    /\ rnd \in 0..Rounds

\* Refinement: extracting lane k from the SIMD state equals base_states[k].
RefinementHolds ==
    \A k \in LaneIdx : base_states[k] = simd_state[k]

Init ==
    /\ base_states = [k \in LaneIdx |-> Init0(k)]
    /\ simd_state = [k \in LaneIdx |-> Init0(k)]
    /\ rnd = 0

\* Lockstep round: both implementations advance one round. Base does
\* N sequential per-lane operations; SIMD does one componentwise
\* operation. The same RoundFn applied to identical pre-state per
\* lane yields identical post-state.
Step ==
    /\ rnd < Rounds
    /\ base_states' = [k \in LaneIdx |-> RoundFn(base_states[k], rnd + 1)]
    /\ simd_state' = [k \in LaneIdx |-> RoundFn(simd_state[k], rnd + 1)]
    /\ rnd' = rnd + 1

Done ==
    /\ rnd = Rounds
    /\ UNCHANGED vars

Next ==
    \/ Step
    \/ Done

Spec == Init /\ [][Next]_vars

THEOREM Spec => [](TypeInvariant /\ RefinementHolds)
====
