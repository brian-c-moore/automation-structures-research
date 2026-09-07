---- MODULE BudgetAuditComposition_Proof ----
EXTENDS BudgetAuditComposition, TLAPS

ASSUME FaultFree == FaultMode = NoFault
ASSUME CapacityNat == Capacity \in Nat
ASSUME CapacityPositive == Capacity > 0
ASSUME MaxRequestNat == MaxRequest \in Nat
ASSUME MaxRequestPositive == MaxRequest > 0
ASSUME FaultValuesDistinct ==
    /\ NoFault /= NoAudit
    /\ NoFault /= Overspend
    /\ NoAudit /= Overspend

Inv == TypeInvariant /\ CompositionInvariant

LEMMA InitInv == Init => Inv
BY CapacityNat, CapacityPositive, MaxRequestNat, MaxRequestPositive
   DEF Init, Inv, TypeInvariant, CompositionInvariant,
       BudgetInvariant, AuditInvariant

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0
       DEF vars, Inv, TypeInvariant, CompositionInvariant,
           BudgetInvariant, AuditInvariant
  <1>1. CASE Reserve
    BY <1>1, CapacityNat, CapacityPositive, MaxRequestNat,
       MaxRequestPositive, FaultFree,
       FaultValuesDistinct
       DEF Reserve, Inv, TypeInvariant, CompositionInvariant,
           BudgetInvariant, AuditInvariant
  <1>2. CASE Reject
    BY <1>2, CapacityNat, CapacityPositive, MaxRequestNat,
       MaxRequestPositive
       DEF Reject, Inv, TypeInvariant, CompositionInvariant,
           BudgetInvariant, AuditInvariant
  <1>3. CASE Commit
    BY <1>3, CapacityNat, CapacityPositive, MaxRequestNat,
       MaxRequestPositive, FaultFree,
       FaultValuesDistinct
       DEF Commit, Inv, TypeInvariant, CompositionInvariant,
           BudgetInvariant, AuditInvariant
  <1>4. CASE Done
    BY <1>4
       DEF Done, vars, Inv, TypeInvariant, CompositionInvariant,
           BudgetInvariant, AuditInvariant
  <1>5. CASE Next
    BY <1>5, <1>1, <1>2, <1>3, <1>4 DEF Next
  <1> QED BY <1>0, <1>5

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv' BY NextInv
  <1>3. QED BY <1>1, <1>2, PTL DEF Spec

THEOREM BudgetSafety == Spec => []BudgetInvariant
  BY Safety, PTL DEF Inv, CompositionInvariant

THEOREM AuditSafety == Spec => []AuditInvariant
  BY Safety, PTL DEF Inv, CompositionInvariant

====
