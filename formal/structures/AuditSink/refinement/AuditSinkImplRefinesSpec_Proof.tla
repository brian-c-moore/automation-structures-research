---- MODULE AuditSinkImplRefinesSpec_Proof ----
EXTENDS AuditSinkImplRefinesSpec, TLAPS

Inv == ImplInvariant
LEMMA InitInv == Init => Inv BY DEF Init, Inv

LEMMA NextInv == Inv /\ [ImplNext]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [ImplNext]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, ImplInvariant, TypeInvariant, ChainIntegrity,
                  HashConsistency, HashBindsContent, LastHashBounded,
                  GenesisConsistency, vars
  <1>1. CASE \E op \in OperationDomain : ImplRecord(op)
    BY <1>1 DEF ImplRecord, Inv
  <1>2. CASE ImplRead
    BY <1>2 DEF ImplRead, Inv, ImplInvariant, TypeInvariant, ChainIntegrity,
                  HashConsistency, HashBindsContent, LastHashBounded,
                  GenesisConsistency, vars
  <1> QED BY <1>0, <1>1, <1>2 DEF ImplNext

THEOREM InvariantSafety == Spec => []Inv
  BY InitInv, NextInv, PTL DEF Spec

LEMMA InitRefines == Init => A!Init BY DEF Init, A!Init

LEMMA NextRefines == [ImplNext]_vars => [A!Next]_(A!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [A!Next]_(A!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, A!vars
  <1>1. CASE \E op \in OperationDomain : ImplRecord(op)
    <2> PICK op \in OperationDomain : ImplRecord(op) BY <1>1
    <2>1. CASE Len(log) < max_log_len
      BY <2>1 DEF ImplRecord, ImplInvariant, TypeInvariant, A!Next, A!Record
    <2>2. CASE ~(Len(log) < max_log_len)
      BY <2>2 DEF ImplRecord, vars, A!vars
    <2> QED BY <2>1, <2>2
  <1>2. CASE ImplRead BY <1>2 DEF ImplRead, vars, A!vars
  <1> QED BY <1>0, <1>1, <1>2 DEF ImplNext

THEOREM RefinementThm == Spec => A!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, A!Spec

THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
