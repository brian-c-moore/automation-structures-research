---- MODULE ReductionStream_NEG_ConsumedPrefixFold ----
\* NEGATIVE CONTROL, generated. Not a specification: this is ReductionStream
\* carrying one deliberate defect, so that a checker fails on it.
\*
\*   base module      : ReductionStream
\*   mutation site    : Consume
\*   target           : ConsumedPrefixFold
\*   required outcome : with only ConsumedPrefixFold declared, TLC MUST report the invariant
\*                      violated. A run that finds no error is a control that has
\*                      stopped measuring.
\*
\* The mutation is delimited by the markers below. Outside them, and
\* apart from the module name, this file is ReductionStream verbatim, less
\* that module's commentary.

EXTENDS Naturals, Sequences

CONSTANTS Src,
          Op(_, _),
          Identity

OpImpl(a, b) == a + b

SrcImpl == <<3, 1, 2>>

FoldPrefix[n \in 0..Len(Src)] ==
    IF n = 0 THEN Identity ELSE Op(FoldPrefix[n - 1], Src[n])

VARIABLES result,
          pos

vars == <<result, pos>>

TypeInvariant ==
    /\ pos \in 0..Len(Src)
    /\ result \in Nat

ConsumedPrefixFold ==
    result = FoldPrefix[pos]

Init ==
    /\ pos = 0
    /\ result = Identity

Consume ==
    /\ pos < Len(Src)
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ UNCHANGED result
    /\ pos' = pos + 1
\* ---- MUTATION ENDS.

Next == Consume

Spec == Init /\ [][Next]_vars

====
