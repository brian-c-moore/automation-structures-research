---- MODULE PolynomialMacEquivalence ----
(*
  Equivalence bridge between the Horner-form (PolynomialMacHornerForm) and
  polynomial-form (PolynomialMacPolynomialForm) polynomial-MAC accumulators.

  The two forms are intended to compute the same polynomial-evaluation value
      M(r) = X_1 * r^N + X_2 * r^(N-1) + ... + X_N * r
  but with different structural orderings - Linear (Horner) vs. DAG
  (polynomial). This module checks one exact finite witness of that bridge:
  P = 7, R = 3, and Blocks = 4. It does not prove the generic algebraic
  identity, equivalence for other parameters, or transfer to a named
  cryptographic algorithm.

  Modeling choice. Both forms' final values are expressed here as
  closed-form non-recursive operators (`HornerAt`, `PolyAt`), unrolled
  for `Blocks <= 4`. Under the exact configured assumptions, TLAPS reduces
  `HornerAt(Blocks) = PolyAt(Blocks)` to a closed modular-arithmetic equality.

  Same field and parameters as the two form modules, so the comparison is
  direct.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS P, R, Blocks

ASSUME PType      == P \in Nat /\ P >= 5
ASSUME RType      == R \in Nat /\ R < P
ASSUME BlocksType == Blocks \in Nat /\ Blocks >= 1 /\ Blocks <= 4
ASSUME PConcrete      == P = 7
ASSUME RConcrete      == R = 3
ASSUME BlocksConcrete == Blocks = 4

Field == 0..(P - 1)
FieldZero == 0
Add(a, b) == (a + b) % P
Mul(a, b) == (a * b) % P

\* Same InputBlock as the two form modules.
InputBlock ==
    [k \in 1..Blocks |->
        IF      k = 1 THEN 1
        ELSE IF k = 2 THEN 2
        ELSE IF k = 3 THEN 3
        ELSE              4]

\* PowerAt(k) = R^k mod P.  Same as PolynomialMacPolynomialForm.
PowerAt(k) ==
    IF      k = 1 THEN R
    ELSE IF k = 2 THEN Mul(R, R)
    ELSE IF k = 3 THEN Mul(Mul(R, R), R)
    ELSE                 Mul(Mul(Mul(R, R), R), R)

LaneProduct(i) == Mul(InputBlock[i], PowerAt(Blocks - i + 1))

\* HornerAt(k) — Horner accumulator after k chain steps.  Unrolled
\* explicitly for Blocks <= 4.
HornerAt(k) ==
    IF      k = 0 THEN FieldZero
    ELSE IF k = 1 THEN Mul(Add(FieldZero, InputBlock[1]), R)
    ELSE IF k = 2 THEN
        Mul(Add(Mul(Add(FieldZero, InputBlock[1]), R), InputBlock[2]), R)
    ELSE IF k = 3 THEN
        Mul(Add(Mul(Add(Mul(Add(FieldZero, InputBlock[1]), R),
                          InputBlock[2]), R),
                  InputBlock[3]), R)
    ELSE
        Mul(Add(Mul(Add(Mul(Add(Mul(Add(FieldZero, InputBlock[1]), R),
                                  InputBlock[2]), R),
                          InputBlock[3]), R),
                  InputBlock[4]), R)

\* PolyAt(k) — polynomial-form sum after k lanes.  Unrolled explicitly.
PolyAt(k) ==
    IF      k = 0 THEN FieldZero
    ELSE IF k = 1 THEN Add(FieldZero, LaneProduct(1))
    ELSE IF k = 2 THEN Add(Add(FieldZero, LaneProduct(1)), LaneProduct(2))
    ELSE IF k = 3 THEN Add(Add(Add(FieldZero, LaneProduct(1)), LaneProduct(2)),
                            LaneProduct(3))
    ELSE              Add(Add(Add(Add(FieldZero, LaneProduct(1)), LaneProduct(2)),
                                LaneProduct(3)), LaneProduct(4))

\* The equivalence claim — a state-independent algebraic identity, packaged
\* as a trivial state machine so TLC can evaluate it as an invariant. The
\* content is in the operator definitions above.
VARIABLES proven
vars == <<proven>>

Init == proven = TRUE
Next == UNCHANGED proven
Spec == Init /\ [][Next]_vars

\* The configured-instance equivalence invariant: both forms yield the same
\* value after four steps at P = 7 and R = 3.
EquivalenceHolds == HornerAt(Blocks) = PolyAt(Blocks)

\* Type invariant (trivial).
TypeInvariant == proven = TRUE

THEOREM Spec => [](TypeInvariant /\ EquivalenceHolds)
====
