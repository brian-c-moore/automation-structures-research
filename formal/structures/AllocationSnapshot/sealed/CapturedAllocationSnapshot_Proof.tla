---- MODULE CapturedAllocationSnapshot_Proof ----
EXTENDS CapturedAllocationSnapshot, TLAPS

Inv == sealed \in BOOLEAN /\ SealedAllocationFixed

LEMMA InitInv == CaptureInit => Inv
  BY DEF CaptureInit, Inv, SealedAllocationFixed

LEMMA NextInv == Inv /\ [CaptureNext]_capture_vars => Inv'
  <1> SUFFICES ASSUME Inv, [CaptureNext]_capture_vars PROVE Inv' OBVIOUS
  <1>1. CASE UNCHANGED capture_vars
    BY <1>1 DEF capture_vars, Inv, SealedAllocationFixed, BudgetObservation, vars
  <1>2. CASE CaptureAccept
    BY <1>2, SMT DEF CaptureAccept, Inv, SealedAllocationFixed
  <1>3. CASE Seal
    BY <1>3, SMT DEF Seal, Inv, SealedAllocationFixed, BudgetObservation, vars
  <1> QED BY <1>1, <1>2, <1>3 DEF CaptureNext

THEOREM SealedAllocationSafety == CaptureSpec => []SealedAllocationFixed
  <1>1. CaptureInit => Inv BY InitInv
  <1>2. Inv /\ [CaptureNext]_capture_vars => Inv' BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF CaptureSpec, Inv
====
