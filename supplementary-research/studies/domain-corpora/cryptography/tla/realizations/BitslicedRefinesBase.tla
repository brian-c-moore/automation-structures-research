---- MODULE BitslicedRefinesBase ----
(*
  Bitsliced realization refines the base iterated-transformation
  composition (refinement of IteratedTransformationOverChainedState).

  Models N inputs flowing through the same iterated-transformation
  state machine, in two parallel implementations:
    Base — N independent state machines (one per input). Each runs
      RoundFn(state, round) at every round; the implementation
      conceptually performs N separate per-input operations.
    Bitsliced — one state machine whose state is an N-tuple (function
      indexed by input slot k in 0..N-1); each round one operation
      updates all N slots simultaneously. In real hardware the slots
      are bits across a wide register; in this abstract model they are
      function-indexed values. The "one operation across N slots" is
      the bitslicing-realization choice.

  Refinement mapping: extract input k from the bitsliced state. For
  every k, base_states[k] = bitsliced_state[k]. The refinement holds
  by construction: both apply the same RoundFn componentwise.

  Mirrors SequentialRefinesStepGraph.tla's refinement-spec idiom, with
  lockstep stepping for a tractable inductive proof. Uses integer arithmetic
  for SMT tractability, as the bridge modules do.

  Modeled instantiation: bitsliced AES-128.
  Bounded parameters per the study definition: N = 4 inputs, Bits = 4.
  The theorem is limited to that configured instance and does not establish
  refinement for other lane counts, bit widths, or concrete AES semantics.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    N,        \* number of parallel inputs
    Bits      \* per-input bit width (used as the state-space bound)

ASSUME NType    == N \in Nat /\ N >= 1 /\ N <= 4
ASSUME BitsType == Bits \in Nat /\ Bits >= 1 /\ Bits <= 4
ASSUME NConcrete    == N = 4
ASSUME BitsConcrete == Bits = 4

\* ── State space (integer representation for SMT tractability) ─────────────
M == 2 ^ Bits                              \* state-space size
ASSUME MConcrete == M = 16
StateValue == 0..(M - 1)
InputSlot == 0..(N - 1)
Rounds == Bits                              \* one round per bit position

\* Per-round transformation. Concrete IF-THEN-ELSE collapsing for SMT:
\* (s + r) % M. Arithmetic operator (not function literal).
RoundFn(s, r) == (s + r) % M

\* Initial state per input slot. Slot k starts at value k.
Init0(k) == k % M

VARIABLES
    base_states,         \* [InputSlot -> StateValue] - one per input
    bitsliced_state,     \* [InputSlot -> StateValue] - the bitsliced tuple
    rnd                  \* shared round counter 0..Rounds

vars == <<base_states, bitsliced_state, rnd>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ base_states \in [InputSlot -> StateValue]
    /\ bitsliced_state \in [InputSlot -> StateValue]
    /\ rnd \in 0..Rounds

\* ---- Safety invariants ---------------------------------------------------

\* Refinement: extract input k from the bitsliced state equals base_states[k].
RefinementHolds ==
    \A k \in InputSlot : base_states[k] = bitsliced_state[k]

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ base_states = [k \in InputSlot |-> Init0(k)]
    /\ bitsliced_state = [k \in InputSlot |-> Init0(k)]
    /\ rnd = 0

\* ---- Actions -------------------------------------------------------------

\* Lockstep round: both implementations advance one round. Base
\* updates each slot via a per-slot operation (conceptually N
\* operations); bitsliced applies one componentwise operation.
Step ==
    /\ rnd < Rounds
    /\ base_states' = [k \in InputSlot |-> RoundFn(base_states[k], rnd + 1)]
    /\ bitsliced_state' = [k \in InputSlot |-> RoundFn(bitsliced_state[k], rnd + 1)]
    /\ rnd' = rnd + 1

\* Terminal: rounds consumed; stutter.
Done ==
    /\ rnd = Rounds
    /\ UNCHANGED vars

Next ==
    \/ Step
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec => [](TypeInvariant /\ RefinementHolds)
====
