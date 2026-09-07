---- MODULE Sequential_Proof ----
(* Carrier-level TLAPS proof for Sequential. The one additional conjunct,
   ActiveBeforeDone, is the inductive fact needed to show that CompleteStep
   cannot advance pc past Steps. It strengthens the proof, not the claim. *)
EXTENDS Sequential, Naturals, Sequences, SequenceTheorems, TLAPS

ActiveBeforeDone == active => pc < Steps
Inv == TypeInvariant /\ HistoryPositionAgreement /\ ActiveBeforeDone

LEMMA InitialValueInDomain ==
    (CHOOSE v \in ValueDomain : TRUE) \in ValueDomain
  <1>1. \E v \in ValueDomain : TRUE  BY ValueDomainNonEmpty
  <1> QED  BY <1>1

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    <2>1. pc \in 0..Steps  BY StepsType DEF Init
    <2>2. value \in ValueDomain  BY InitialValueInDomain DEF Init
    <2>3. active \in BOOLEAN  BY DEF Init
    <2>4. history \in Seq(ValueDomain)  BY DEF Init
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF TypeInvariant
  <1>2. HistoryPositionAgreement
    BY DEF Init, HistoryPositionAgreement
  <1>3. ActiveBeforeDone
    BY DEF Init, ActiveBeforeDone
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, HistoryPositionAgreement,
              ActiveBeforeDone
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE BeginStep
    <2>1. pc' = pc /\ value' = value /\ history' = history /\ active' = TRUE
      BY <1>A DEF BeginStep, vars
    <2>2. pc < Steps
      BY <1>A DEF BeginStep
    <2> QED  BY <2>1, <2>2
  <1>B. CASE CompleteStep
    <2>1. pc < Steps
      BY <1>B DEF Inv, ActiveBeforeDone, CompleteStep
    <2>2. pc' = pc + 1 /\ active' = FALSE
      BY <1>B DEF CompleteStep
    <2>3. \E v \in ValueDomain : value' = v /\ history' = Append(history, v)
      BY <1>B DEF CompleteStep
    <2>4. pc' \in 0..Steps
      BY <2>1, <2>2, StepsType
    <2>5. value' \in ValueDomain
      BY <2>3
    <2>6. history' \in Seq(ValueDomain)
      BY <2>3, AppendProperties
    <2>7. Len(history') = pc'
      BY <2>2, <2>3, AppendProperties
    <2> QED  BY <2>2, <2>4, <2>5, <2>6, <2>7
  <1>C. CASE DoneStuttering
    BY <1>C DEF DoneStuttering, vars
  <1>D. CASE Next
    BY <1>D, <1>A, <1>B, <1>C DEF Next
  <1> QED  BY <1>0, <1>D

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                   BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'   BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv
THEOREM HistoryPositionAgreementSafety == Spec => []HistoryPositionAgreement
  BY Safety, PTL DEF Inv

THEOREM TotalOrderSafety == Spec => []TotalOrder
  BY HistoryPositionAgreementSafety, PTL DEF TotalOrder
====
