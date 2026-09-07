---- MODULE ReductionSummary_Proof ----
\* The ordered consumer calls the same summary Record. No reassociation,
\* arbitrary typed Rust operator, or batch-ingestion implementation is claimed.
EXTENDS ReductionSummary, AuditSinkSummary_Proof

LEMMA ReductionInitRefines == Init => RS!Init BY DEF Init, RS!Init

LEMMA ReductionNextRefines == [ReductionNext]_vars => [RS!Next]_(RS!vars)
  <1> SUFFICES ASSUME [ReductionNext]_vars
               PROVE [RS!Next]_(RS!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, RS!vars
  <1>1. CASE Consume
    BY <1>1 DEF Consume, Record, CompactRecord, RS!Next, RS!Consume
  <1>2. CASE count = Len(Source) /\ UNCHANGED vars
    BY <1>2 DEF vars, RS!vars
  <1> QED BY <1>0, <1>1, <1>2 DEF ReductionNext

THEOREM ReductionRefinementThm == ReductionSpec => ReductionRefinement
  BY ReductionInitRefines, ReductionNextRefines, PTL
    DEF ReductionSpec, ReductionRefinement, RS!Spec

LEMMA ReductionUsesSummary == [ReductionNext]_vars => [Next]_vars
  BY DEF ReductionNext, Consume, Record, CompactRecord, Next

THEOREM ReductionSummaryBehavior == ReductionSpec => Spec
  BY ReductionUsesSummary, PTL DEF ReductionSpec, Spec

THEOREM ReductionSummarySafety == ReductionSpec => []Inv /\ AuditRefinement
  BY ReductionSummaryBehavior, SummarySafety, Refinement, PTL
====
