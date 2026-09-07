---- MODULE SignalSummary_Proof ----
\* Same summary owner plus bounded listener positions. This proves the logical
\* latest-change/catch-up protocol, not physical synchronization or wait reuse.
\* Set/cursor proof order follows SignalFromAuditSink_Proof.
EXTENDS SignalSummary, AuditSinkSummary_Proof

SignalInv == Inv /\ CursorBound

LEMMA SignalInitInv == SignalInit => SignalInv
  BY InitInv DEF SignalInit, SignalInv, CursorBound, Init

LEMMA SignalNextInv == SignalInv /\ [SignalNext]_signalVars => SignalInv'
  <1> SUFFICES ASSUME SignalInv, [SignalNext]_signalVars
               PROVE SignalInv' OBVIOUS
  <1>old. /\ Inv
          /\ count \in Nat
          /\ cursor \in [Listeners -> 0..count]
    BY DEF SignalInv, Inv, BasicTypes, CursorBound
  <1>0. CASE UNCHANGED signalVars
    BY <1>0 DEF signalVars, SignalInv, Inv, BasicTypes, SummaryBinding,
               CountBinding, CarryBinding, LatestBinding, CapacityBound, CursorBound
  <1>1. CASE \E value \in Operations : SetValue(value)
    <2> PICK value \in Operations : SetValue(value) BY <1>1
    <2>owner. Inv' BY <1>old, RecordInv DEF SetValue
    <2>step. count' = count + 1 /\ cursor' = cursor
      BY DEF SetValue, Record, CompactRecord
    <2>bound. CursorBound' BY <1>old, <2>step DEF CursorBound
    <2> QED BY <2>owner, <2>bound DEF SignalInv
  <1>2. CASE \E listener \in Listeners : NotifyListener(listener)
    <2> PICK listener \in Listeners : NotifyListener(listener) BY <1>2
    <2>step. /\ cursor' = [cursor EXCEPT ![listener] = count]
             /\ UNCHANGED vars
      BY DEF NotifyListener
    <2>owner. Inv'
      BY <1>old, <2>step DEF vars, Inv, BasicTypes, SummaryBinding,
                               CountBinding, CarryBinding, LatestBinding, CapacityBound
    <2>bound. CursorBound' BY <1>old, <2>step DEF CursorBound, vars
    <2> QED BY <2>owner, <2>bound DEF SignalInv
  <1>3. CASE (\E value \in Operations : RefusedSet(value))
             \/ (\E listener \in Listeners : RefusedNotify(listener))
    BY <1>3 DEF RefusedSet, RefusedNotify, signalVars, SignalInv, Inv,
               BasicTypes, SummaryBinding, CountBinding, CarryBinding,
               LatestBinding, CapacityBound, CursorBound
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF SignalNext

THEOREM SignalSummarySafety == SignalSpec => []SignalInv
  BY SignalInitInv, SignalNextInv, PTL DEF SignalSpec

LEMMA SignalInitRefines == SignalInit => Sig!Init
  BY InitialValueType DEF SignalInit, Init, Sig!Init, CurrentValue, MapPending, MapNotified

LEMMA SignalNextRefines ==
    SignalInv /\ [SignalNext]_signalVars => [Sig!Next]_(Sig!vars)
  <1> SUFFICES ASSUME SignalInv, [SignalNext]_signalVars
               PROVE [Sig!Next]_(Sig!vars) OBVIOUS
  <1>old. /\ count \in Nat
          /\ cursor \in [Listeners -> 0..count]
    BY DEF SignalInv, Inv, BasicTypes, CursorBound
  <1>0. CASE UNCHANGED signalVars
    BY <1>0 DEF signalVars, Sig!vars, CurrentValue, MapPending, MapNotified
  <1>1. CASE \E value \in Operations : SetValue(value)
    <2> PICK value \in Operations : SetValue(value) BY <1>1
    <2>step. /\ value /= CurrentValue
             /\ latest' = <<value>>
             /\ count' = count + 1
             /\ cursor' = cursor
      BY DEF SetValue, Record, CompactRecord
    <2>value. CurrentValue' = value BY <2>step DEF CurrentValue
    <2>pending. MapPending' = Listeners
      BY <1>old, <2>step DEF MapPending
    <2>notified. MapNotified' = {}
      BY <1>old, <2>step DEF MapNotified
    <2>action. Sig!SetValue(value)
      BY <1>old, <2>step, <2>value, <2>pending, <2>notified DEF Sig!SetValue
    <2> QED BY <2>action DEF Sig!Next
  <1>2. CASE \E listener \in Listeners : NotifyListener(listener)
    <2> PICK listener \in Listeners : NotifyListener(listener) BY <1>2
    <2>step. /\ cursor[listener] < count
             /\ cursor' = [cursor EXCEPT ![listener] = count]
             /\ UNCHANGED vars
      BY DEF NotifyListener
    <2>positions. \A l \in Listeners :
        cursor'[l] = IF l = listener THEN count ELSE cursor[l]
      BY <1>old, <2>step
    <2>positive. count > 0 BY <1>old, <2>step
    <2>pending. MapPending' = MapPending \ {listener}
      BY <1>old, <2>step, <2>positions DEF MapPending, vars
    <2>notified. MapNotified' = MapNotified \cup {listener}
      BY <1>old, <2>step, <2>positions, <2>positive DEF MapNotified, vars
    <2>value. CurrentValue' = CurrentValue BY <2>step DEF vars, CurrentValue
    <2>action. Sig!NotifyListener(listener)
      BY <2>step, <2>pending, <2>notified, <2>value
        DEF Sig!NotifyListener, MapPending, vars
    <2> QED BY <2>action DEF Sig!Next
  <1>3. CASE (\E value \in Operations : RefusedSet(value))
             \/ (\E listener \in Listeners : RefusedNotify(listener))
    BY <1>3 DEF RefusedSet, RefusedNotify, signalVars, Sig!vars,
               CurrentValue, MapPending, MapNotified
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF SignalNext

THEOREM SignalRefinementThm == SignalSpec => SignalRefinement
  BY SignalInitRefines, SignalNextRefines, SignalSummarySafety, PTL
    DEF SignalSpec, SignalRefinement, Sig!Spec

LEMMA SignalUsesSummary == [SignalNext]_signalVars => [Next]_vars
  BY DEF SignalNext, SetValue, NotifyListener, RefusedSet, RefusedNotify,
         signalVars, vars, Next

THEOREM SignalSummaryBehavior == SignalSpec => Spec
  BY SignalUsesSummary, PTL DEF SignalSpec, SignalInit, Spec

THEOREM SignalAuditRefinement == SignalSpec => AuditRefinement
  BY SignalSummaryBehavior, Refinement, PTL
====
