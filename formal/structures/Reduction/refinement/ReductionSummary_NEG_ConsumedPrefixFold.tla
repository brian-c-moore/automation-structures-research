---- MODULE ReductionSummary_NEG_ConsumedPrefixFold ----
\* Ordered-prefix observation of the same AuditSink summary profile.
\* Immutable Source is logical configuration, not a claimed streaming buffer.
\* Noncommutative finite operator catches order loss without associativity.
EXTENDS AuditSinkSummary

CONSTANT Source
ConfiguredSource == <<3, 1, 2, 3>>
OrderedOp(previous, operation) == previous * 4 + operation

ASSUME SourceType == Source \in Seq(Operations)
ASSUME LifetimeBound == MaxLogLen = Len(Source)

RS == INSTANCE ReductionStream WITH
    Src <- Source, Op <- Hash, Identity <- 0, result <- carry, pos <- count

Consume ==
    /\ count < Len(Source)
    /\ Record(Source[Len(Source) - count])

ReductionNext == Consume \/ (count = Len(Source) /\ UNCHANGED vars)
ReductionSpec == Init /\ [][ReductionNext]_vars

ConsumedPrefixFold == RS!ConsumedPrefixFold
ReductionRefinement == RS!Spec
====
