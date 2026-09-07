---- MODULE PolynomialMacHornerForm ----
(*
  Polynomial-MAC accumulation, Horner form.

  Split out of the single polynomial-MAC module per the project's
  decomposition-for-large-specs standard. This file establishes the
  Horner-form invariant; sibling files establish the polynomial-form
  invariant and the equivalence bridge:
    - PolynomialMacHornerForm.tla     (this file)
    - PolynomialMacPolynomialForm.tla (inherits this file's field typing)
    - PolynomialMacEquivalence.tla    (bridges the two via
                                       Reduction-associativity)

  Pattern. Polynomial-MAC accumulation evaluates the polynomial
      M(r) = X_1 * r^N + X_2 * r^(N-1) + ... + X_N * r
  at a fixed point r, using Horner's rule:
      A <- 0; A <- (A + X_i) * r for i = 1..N
  Linear ordering: each step depends on the prior. The accumulator after
  step i equals the polynomial-evaluation prefix evaluated through X_i.

  Canonical examples: GHASH (in AES-GCM), Poly1305 (standalone).

  Build requirements demonstrated: ResourceRegistry (accumulator + history)
    + TraversalEngine (over input blocks) + ActuationPass (per-step
    Horner combine). Field arithmetic (Add, Mul) is uninterpreted
    cryptographic content; the structural correctness of the pattern is
    independent of the particular field.

  Safety claims:
    HistoryStartsAtZero — history[1] = FieldZero (the Horner-form anchor).
    HornerChainConsistent — each consecutive accumulator step satisfies
      history[k+1] = Mul(Add(history[k], InputBlock[k]), r). The chain
      cannot be parallelized.
    ChainedAccCorrect — accumulator equals history[Len(history)].

  Bounded parameters per the study definition: Blocks = 4, Field = GF(7).
  Exhaustive.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    P,             \* field modulus (prime); the .cfg sets P = 7
    R,             \* the polynomial evaluation point (the "key" r in Horner)
    Blocks         \* number of input blocks to accumulate

\* P >= 5 because the concrete InputBlock values include {1, 2, 3, 4}; the
\* type invariant InputBlock[k] \in Field requires all of those to be < P.
ASSUME PType      == P \in Nat /\ P >= 5
ASSUME RType      == R \in Nat /\ R < P
ASSUME BlocksType == Blocks \in Nat /\ Blocks >= 1

\* ── Fixed topology ───────────────────────────────────────────────────────
Field == 0..(P - 1)
FieldZero == 0

\* Field operations: Add and Mul mod P. Defined via standard Nat arithmetic
\* using the % operator from the Naturals module.
Add(a, b) == (a + b) % P
Mul(a, b) == (a * b) % P

\* InputBlock: 1..Blocks -> Field.  The polynomial coefficients X_i (mapped
\* to field elements). Concrete content; the proof's structural correctness
\* is independent.
InputBlock ==
    [k \in 1..Blocks |->
        IF      k = 1 THEN 1
        ELSE IF k = 2 THEN 2
        ELSE IF k = 3 THEN 3
        ELSE              4]

VARIABLES
    accumulator,   \* Field — current Horner accumulator
    idx,           \* 0..Blocks (number of steps taken)
    history        \* Seq(Field) — chain of accumulator states

vars == <<accumulator, idx, history>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ accumulator \in Field
    /\ idx \in 0..Blocks
    /\ history \in Seq(Field)
    /\ Len(history) = idx + 1

\* ---- Safety invariants ---------------------------------------------------

HistoryStartsAtZero == history[1] = FieldZero

HornerChainConsistent ==
    \A k \in 1..idx :
        history[k + 1] = Mul(Add(history[k], InputBlock[k]), R)

ChainedAccCorrect == accumulator = history[Len(history)]

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ accumulator = FieldZero
    /\ idx = 0
    /\ history = <<FieldZero>>

\* ---- Actions -------------------------------------------------------------

HornerStep ==
    /\ idx < Blocks
    /\ LET next == Mul(Add(accumulator, InputBlock[idx + 1]), R)
       IN  /\ accumulator' = next
           /\ history' = Append(history, next)
    /\ idx' = idx + 1

Done ==
    /\ idx = Blocks
    /\ UNCHANGED vars

Next ==
    \/ HornerStep
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec =>
    [](TypeInvariant /\ HistoryStartsAtZero
       /\ HornerChainConsistent /\ ChainedAccCorrect)
====
