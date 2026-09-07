---- MODULE HardwareAcceleratedRefinesBase ----
(*
  Hardware-accelerated realization refines the base
  iterated-transformation composition (refinement of
  IteratedTransformationOverChainedState).

  Models one input flowing through the iterated-transformation state
  machine in two parallel implementations:
    Base — per round, ActuationPass takes multiple sub-steps, modelled
      as a single round operation `RoundFn(state, r)` that conceptually
      unfolds to SubBytes/ShiftRows/MixColumns/AddRoundKey in real AES.
      At the spec-level granularity both Base and HW take one state
      transition per round; Base's per-round work is multi-cycle and the
      multi-step structure is not modelled.
    HW — per round, a single hardware-accelerated instruction (e.g.,
      AES-NI's `aesenc`) computes the same round-output in one cycle.
      Modelled as the same `RoundFn` applied in one step.

  Refinement mapping: identity on state. Base and HW carry the same
  state at every round boundary. The realization choice (hardware
  acceleration) is a composition choice within the build (one
  instruction substitutes for the multi-cycle sequence); it is not a
  build-requirement change. Functional equivalence: identical outputs.

  Mirrors BitslicedRefinesBase's lockstep refinement pattern.
  Uses integer arithmetic for SMT tractability.

  Modeled instantiation: AES-128 round vs AES-NI aesenc.
  Bounded parameters per the study definition: Rounds = 4 (model bound;
  real AES-128 has 10).
  The theorem is limited to Rounds = 4 and Bits = 4 in this abstract
  lockstep model; it does not establish concrete AES or AES-NI semantics.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Rounds,    \* round count (small bound for the model)
    Bits       \* per-state bit width

ASSUME RoundsType == Rounds \in Nat /\ Rounds >= 1 /\ Rounds <= 4
ASSUME BitsType   == Bits \in Nat /\ Bits >= 1 /\ Bits <= 4
ASSUME RoundsConcrete == Rounds = 4
ASSUME BitsConcrete   == Bits = 4

M == 2 ^ Bits
ASSUME MConcrete == M = 16
StateValue == 0..(M - 1)

\* Per-round transformation. The "multi-step" structure (SubBytes,
\* ShiftRows, MixColumns, AddRoundKey) is conceptual; at the abstract
\* level both Base and HW apply the same composite function.
RoundFn(s, r) == (s + r) % M

\* Initial state.
Init0 == 0

VARIABLES
    base_state,         \* state of the base (multi-step ActuationPass) version
    hw_state,           \* state of the HW-accelerated version
    rnd                 \* shared round counter 0..Rounds

vars == <<base_state, hw_state, rnd>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ base_state \in StateValue
    /\ hw_state \in StateValue
    /\ rnd \in 0..Rounds

\* ---- Safety invariants ---------------------------------------------------

\* Refinement: base and HW carry the same state.
RefinementHolds == base_state = hw_state

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ base_state = Init0
    /\ hw_state = Init0
    /\ rnd = 0

\* ---- Actions -------------------------------------------------------------

\* Lockstep round: both implementations advance one round. Base
\* conceptually runs through multiple sub-steps within RoundFn; HW
\* completes the same transformation in one hardware instruction.
\* TLA+ models the per-round result; the multi-step / single-step
\* distinction is a refinement-of-realization claim documented in
\* the header.
Step ==
    /\ rnd < Rounds
    /\ base_state' = RoundFn(base_state, rnd + 1)
    /\ hw_state' = RoundFn(hw_state, rnd + 1)
    /\ rnd' = rnd + 1

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
