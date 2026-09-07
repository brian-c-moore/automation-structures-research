---- MODULE PropagationPassNotRequired ----
(*
  PropagationPass is not required by the cryptographic build
  (the composition taxonomy unused-primitive demonstration).

  Framing (load-bearing — preserve per the study framing §2).
  This is not a claim that PropagationPass *cannot* fit cryptography;
  it is the weaker, accurate claim that *you don't need it to build
  the fifteen algorithms*. The framework makes no exclusion claims.

  Demonstration. PropagationPass terminates on fixed-point detection
  via a delta-based stopping condition. Cryptographic algorithms have
  fixed iteration bounds (SHA-256: 64 rounds; AES-128: 10 rounds;
  etc.). We model a composition that attempts PropagationPass with a
  delta criterion `delta(state, state') = 0` (state stops changing) and
  observe that for the cryptographic round structure either:
    (a) the delta criterion does not naturally fire at the prescribed
        round count (round-by-round state changes by design), so an
        external counter overrides the delta condition — meaning the
        counter does the work and PropagationPass is decorative; OR
    (b) the delta criterion is reverse-engineered to fire exactly at
        the prescribed round count, encoding what TraversalEngine
        naturally provides.

  Modelled instantiation. A small iterated-transformation composition
  with `TargetRounds = 4` and a `PropagationStep` action whose
  termination guard is `round = TargetRounds`. The delta-based check
  is vacuous (the round-counter check subsumes it). The cfg-verified
  invariant: the termination round always equals `TargetRounds`.

  `PropagationPassNotRequired_Proof.tla` proves the stated invariant;
  the finite configuration checks the bounded instance.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets

CONSTANTS
    TargetRounds

ASSUME TargetRoundsType == TargetRounds \in Nat /\ TargetRounds >= 1

\* Minimal value space.
StateValue == 0..3

\* Iterated-transformation per round (concrete operator).
RoundFn(s) == (s + 1) % 4

VARIABLES
    state,           \* current state value
    round,           \* round counter 0..TargetRounds
    terminated       \* TRUE once the composition stops

vars == <<state, round, terminated>>

TypeInvariant ==
    /\ state \in StateValue
    /\ round \in 0..TargetRounds
    /\ terminated \in BOOLEAN

\* The point of the demonstration: termination is driven by the round
\* counter (TraversalEngine), not by a delta criterion. When
\* terminated, round = TargetRounds.
TerminationFromCounter ==
    terminated => round = TargetRounds

Init ==
    /\ state = 0
    /\ round = 0
    /\ terminated = FALSE

\* PropagationStep models the attempted PropagationPass step. The
\* "delta criterion" would be `state = state'`, but RoundFn always
\* changes the state (cryptographic round structure guarantees
\* state-change every round); so the delta criterion never fires
\* and termination must come from elsewhere — namely the round
\* counter.
PropagationStep ==
    /\ ~terminated
    /\ round < TargetRounds
    /\ state' = RoundFn(state)
    /\ round' = round + 1
    /\ UNCHANGED terminated

\* Termination via the round counter (the only way termination can
\* occur, since delta never fires).
Terminate ==
    /\ ~terminated
    /\ round = TargetRounds
    /\ terminated' = TRUE
    /\ UNCHANGED <<state, round>>

Done ==
    /\ terminated
    /\ UNCHANGED vars

Next ==
    \/ PropagationStep
    \/ Terminate
    \/ Done

Spec == Init /\ [][Next]_vars

THEOREM Spec => [](TypeInvariant /\ TerminationFromCounter)
====
