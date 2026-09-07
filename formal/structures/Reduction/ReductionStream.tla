---- MODULE ReductionStream ----
(* Ordered-stream reduction with an explicit consumed-prefix position.

   ConsumedPrefixFold requires result to equal the Op/Identity fold of exactly
   the consumed prefix. The independent result and position variables make a
   duplicated combination or an unmatched position advance falsifiable;
   ReductionStreamDecomposed isolates that split.

   Src, Op, and Identity are domain parameters. The proof states the algebraic
   premises it consumes. The TLC configuration supplies a finite source and
   addition instance because a sequence value cannot be written directly as a
   TLC constant. Multiplicity, ordering, and exactly-once contribution are
   represented; concurrent scheduling beyond the decomposed witness is not.  *)
EXTENDS Naturals, Sequences

CONSTANTS Src,        \* the source stream: a sequence of values
          Op(_, _),   \* the associative combine (a domain parameter)
          Identity    \* its two-sided identity

\* Concrete operator realization for TLC.
OpImpl(a, b) == a + b

\* One finite stream with nonuniform contributions.
SrcImpl == <<3, 1, 2>>

\* The fold of the first n elements of the stream.
FoldPrefix[n \in 0..Len(Src)] ==
    IF n = 0 THEN Identity ELSE Op(FoldPrefix[n - 1], Src[n])

VARIABLES result,   \* the running summary
          pos       \* how much of the stream has been consumed

vars == <<result, pos>>

TypeInvariant ==
    /\ pos \in 0..Len(Src)
    /\ result \in Nat

\* `result` is the fold of exactly the consumed prefix:
\* every element contributes exactly once, and the summary is the fold of the
\* contributions.
ConsumedPrefixFold ==
    result = FoldPrefix[pos]

Init ==
    /\ pos = 0
    /\ result = Identity

\* Consume the next element: combine its value into the summary and advance
\* past it, in one step. Splitting these is ReductionStreamDecomposed.
Consume ==
    /\ pos < Len(Src)
    /\ result' = Op(result, Src[pos + 1])
    /\ pos' = pos + 1

Next == Consume

Spec == Init /\ [][Next]_vars

\* Spec => []TypeInvariant, []ConsumedPrefixFold: proved in
\* ReductionStream_Proof.tla.
====
