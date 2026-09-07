---- MODULE AuditSinkSummary_Proof ----
\* Parametric logical-history refinement; no implementation or audit-custody claim.
\* Proof idioms: AuditSinkImplRefinesSpec_Proof and the typed AppendProperties
\* steps of BacktrackingTraversalUndoFromAuditSink_Proof. No HashCR premise.
EXTENDS AuditSinkSummary, SequenceTheorems, TLAPS

ASSUME CapacityType == MaxLogLen \in Nat
ASSUME HashType == \A previous \in Nat, operation \in Operations :
    Hash(previous, operation) \in Nat

Inv == BasicTypes /\ SummaryBinding /\ CapacityBound

LEMMA InitInv == Init => Inv
  BY CapacityType DEF Init, Inv, BasicTypes, SummaryBinding,
                      CountBinding, CarryBinding, LatestBinding, CapacityBound, Entry

LEMMA RecordInv ==
    ASSUME NEW operation \in Operations, Inv, Record(operation)
    PROVE Inv'
  <1> DEFINE entry == [operation |-> operation, prev_hash |-> carry,
                       hash |-> Hash(carry, operation)]
  <1>old. /\ history \in Seq(Entry)
          /\ count \in Nat
          /\ carry \in Nat
          /\ count = Len(history)
    BY DEF Inv, BasicTypes, SummaryBinding, CountBinding
  <1>step. /\ history' = Append(history, entry)
           /\ count' = count + 1
           /\ carry' = Hash(carry, operation)
           /\ latest' = <<operation>>
           /\ count < MaxLogLen
    BY DEF Record, CompactRecord, LogicalHistoryStep
  <1>hash. Hash(carry, operation) \in Nat BY <1>old, HashType
  <1>entry. entry \in Entry BY <1>old, <1>hash DEF Entry
  <1>append. /\ history' \in Seq(Entry)
             /\ Len(history') = Len(history) + 1
             /\ history'[Len(history) + 1] = entry
    BY <1>step, <1>entry, <1>old, AppendProperties
  <1>types. BasicTypes'
    BY <1>old, <1>step, <1>hash, <1>append DEF BasicTypes
  <1>count. CountBinding'
    BY <1>old, <1>step, <1>append DEF CountBinding
  <1>carry. CarryBinding'
    BY <1>old, <1>step, <1>append DEF CarryBinding
  <1>latest. LatestBinding'
    BY <1>old, <1>step, <1>append DEF LatestBinding
  <1>bound. CapacityBound'
    BY <1>old, <1>step, CapacityType DEF CapacityBound
  <1> QED BY <1>types, <1>count, <1>carry, <1>latest, <1>bound
    DEF Inv, SummaryBinding

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars, Inv, BasicTypes, SummaryBinding,
               CountBinding, CarryBinding, LatestBinding, CapacityBound
  <1>1. CASE \E operation \in Operations : Record(operation)
    BY <1>1, RecordInv
  <1>2. CASE \E operation \in Operations : RefusedRecord(operation)
    BY <1>2 DEF RefusedRecord, vars, Inv, BasicTypes, SummaryBinding,
               CountBinding, CarryBinding, LatestBinding, CapacityBound
  <1> QED BY <1>0, <1>1, <1>2 DEF Next

THEOREM SummarySafety == Spec => []Inv
  BY InitInv, NextInv, PTL DEF Spec

LEMMA InitRefines == Init => AS!Init BY DEF Init, AS!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [AS!Next]_(AS!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars
               PROVE [AS!Next]_(AS!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, AS!vars
  <1>1. CASE \E operation \in Operations : Record(operation)
    BY <1>1 DEF Inv, SummaryBinding, CountBinding, Record,
               CompactRecord, LogicalHistoryStep, AS!Next, AS!Record
  <1>2. CASE \E operation \in Operations : RefusedRecord(operation)
    BY <1>2 DEF RefusedRecord, vars, AS!vars
  <1> QED BY <1>0, <1>1, <1>2 DEF Next

THEOREM Refinement == Spec => AuditRefinement
  BY InitRefines, NextRefines, SummarySafety, PTL
    DEF Spec, AuditRefinement, AS!Spec

LEMMA GuardFromInv == Inv => GuardAgreement
  BY DEF Inv, SummaryBinding, CountBinding, GuardAgreement

THEOREM AdmissionAgreement == Spec => []GuardAgreement
  BY SummarySafety, GuardFromInv, PTL
====
