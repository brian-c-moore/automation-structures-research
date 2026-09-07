---- MODULE DepthDerivedBacktracking_Proof ----
(* Inductive safety proof for the depth-derived target.

   The theorem proves only the target's four registered state predicates:
   TypeInvariant, DepthCoupling, DerivedStack, and RecordedLeavesValid. It does
   not establish model adequacy for arbitrary do/undo traversal, progress, or
   a refinement from the pure-connective construction.                     *)
EXTENDS DepthDerivedBacktracking, Naturals, Sequences, SequenceTheorems, TLAPS

ASSUME BranchFactorType == BranchFactor \in Nat
ASSUME MaxDepthType == MaxDepth \in Nat
ASSUME InitAuxType == InitAux \in Nat

Inv ==
    /\ TypeInvariant
    /\ DepthCoupling
    /\ DerivedStack
    /\ RecordedLeavesValid

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv OBVIOUS
<1> USE DEF Init, Depth
<1>1. TypeInvariant
    BY MaxDepthType, InitAuxType DEF TypeInvariant
<1>2. DepthCoupling
    BY InitAuxType DEF DepthCoupling
<1>3. DerivedStack
    BY DEF DerivedStack
<1>4. RecordedLeavesValid
    BY DEF RecordedLeavesValid
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
<1> USE DEF Inv, TypeInvariant, DepthCoupling, DerivedStack,
            RecordedLeavesValid, Depth, IsLeaf
<1>nat. /\ path \in Seq(1..BranchFactor)
        /\ aux_stack \in Seq(Nat)
        /\ aux \in Nat
        /\ Len(path) \in Nat
        /\ Len(aux_stack) \in Nat
        /\ Len(aux_stack) = Len(path)
        /\ Len(path) <= MaxDepth
        /\ path \in [1..Len(path) -> 1..BranchFactor]
        /\ aux_stack \in [1..Len(aux_stack) -> Nat]
    BY LenProperties DEF TypeInvariant
<1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
<1>1. CASE \E c \in 1..BranchFactor : Descend(c)
    <2> SUFFICES ASSUME NEW c \in 1..BranchFactor, Descend(c) PROVE Inv'
        BY <1>1
    <2>nl. Len(path) # MaxDepth BY DEF Descend
    <2>pa. path' = Append(path, c) BY DEF Descend
    <2>sa. aux_stack' = Append(aux_stack, aux) BY DEF Descend
    <2>aa. aux' = aux + 1 BY DEF Descend
    <2>va. visited' = visited BY DEF Descend
    <2>ap. /\ path' \in Seq(1..BranchFactor)
           /\ Len(path') = Len(path) + 1
           /\ \A i \in 1..Len(path) : path'[i] = path[i]
           /\ path'[Len(path) + 1] = c
        BY <2>pa, <1>nat, AppendProperties
    <2>as. /\ aux_stack' \in Seq(Nat)
           /\ Len(aux_stack') = Len(aux_stack) + 1
           /\ \A i \in 1..Len(aux_stack) : aux_stack'[i] = aux_stack[i]
           /\ aux_stack'[Len(aux_stack) + 1] = aux
        BY <2>sa, <1>nat, AppendProperties
    <2>1. TypeInvariant'
        <3>1. path' \in Seq(1..BranchFactor) BY <2>ap
        <3>2. Len(path') <= MaxDepth
            BY <2>ap, <2>nl, <1>nat, MaxDepthType
        <3>3. aux' \in Nat BY <2>aa, <1>nat
        <3>4. aux_stack' \in Seq(Nat) BY <2>as
        <3>5. Len(aux_stack') = Len(path') BY <2>ap, <2>as, <1>nat
        <3>6. visited' \subseteq Seq(1..BranchFactor)
            BY <2>va DEF TypeInvariant
        <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
            DEF TypeInvariant
    <2>2. DepthCoupling'
        BY <2>aa, <2>ap, <1>nat, InitAuxType DEF DepthCoupling
    <2>3. DerivedStack'
        <3> SUFFICES ASSUME NEW i \in 1..Len(path')
                     PROVE aux_stack'[i] = InitAux + (i - 1)
            BY <2>ap DEF DerivedStack
        <3>1. CASE i \in 1..Len(path)
            <4>1. aux_stack'[i] = aux_stack[i]
                BY <3>1, <2>as, <1>nat
            <4>2. aux_stack[i] = InitAux + (i - 1)
                BY <3>1, <1>nat DEF DerivedStack
            <4> QED BY <4>1, <4>2
        <3>2. CASE i = Len(path) + 1
            <4>1. aux_stack'[i] = aux BY <3>2, <2>as, <1>nat
            <4>2. aux = InitAux + Len(path) BY DEF DepthCoupling
            <4>3. i - 1 = Len(path) BY <3>2, <1>nat
            <4> QED BY <4>1, <4>2, <4>3
        <3> QED BY <3>1, <3>2, <2>ap, <1>nat
    <2>4. RecordedLeavesValid'
        BY <2>va DEF RecordedLeavesValid
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv
<1>2. CASE Visit
    <2>leaf. Len(path) = MaxDepth BY <1>2 DEF Visit
    <2>vv. visited' = visited \cup {path} BY <1>2 DEF Visit
    <2>uc. path' = path /\ aux' = aux /\ aux_stack' = aux_stack
        BY <1>2 DEF Visit
    <2>1. TypeInvariant'
        BY <2>uc, <2>vv, <1>nat DEF TypeInvariant
    <2>2. DepthCoupling'
        BY <2>uc DEF DepthCoupling
    <2>3. DerivedStack'
        BY <2>uc DEF DerivedStack
    <2>4. RecordedLeavesValid'
        <3> SUFFICES ASSUME NEW p \in visited'
                     PROVE /\ Len(p) = MaxDepth
                           /\ \A i \in 1..MaxDepth :
                                  p[i] \in 1..BranchFactor
            BY DEF RecordedLeavesValid
        <3>1. CASE p \in visited
            BY <3>1 DEF RecordedLeavesValid
        <3>2. CASE p = path
            <4>1. Len(p) = MaxDepth BY <3>2, <2>leaf
            <4>2. \A i \in 1..MaxDepth : p[i] \in 1..BranchFactor
                BY <3>2, <2>leaf, <1>nat
            <4> QED BY <4>1, <4>2
        <3> QED BY <3>1, <3>2, <2>vv
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv
<1>3. CASE Ascend
    <2>d1. Len(path) >= 1 BY <1>3 DEF Ascend
    <2>av. aux' = aux_stack[Len(path)] BY <1>3 DEF Ascend
    <2>sv. aux_stack' = SubSeq(aux_stack, 1, Len(path) - 1)
        BY <1>3 DEF Ascend
    <2>pv. path' = SubSeq(path, 1, Len(path) - 1)
        BY <1>3 DEF Ascend
    <2>uv. visited' = visited BY <1>3 DEF Ascend
    <2>psub. \A i \in 1..(Len(path) - 1) :
                   path[i] \in 1..BranchFactor
        BY <1>nat
    <2>ssub. \A i \in 1..(Len(path) - 1) : aux_stack[i] \in Nat
        BY <1>nat
    <2>sp. /\ path' \in Seq(1..BranchFactor)
           /\ Len(path') = Len(path) - 1
           /\ \A i \in 1..(Len(path) - 1) : path'[i] = path[i]
        <3>1. /\ SubSeq(path, 1, Len(path) - 1) \in
                       Seq(1..BranchFactor)
              /\ Len(SubSeq(path, 1, Len(path) - 1)) =
                     (IF 1 <= Len(path) - 1
                      THEN (Len(path) - 1) - 1 + 1
                      ELSE 0)
              /\ \A i \in 1..(Len(path) - 1) - 1 + 1 :
                     SubSeq(path, 1, Len(path) - 1)[i] = path[1 + i - 1]
            BY <2>psub, <1>nat, SubSeqProperties
        <3> QED BY <3>1, <2>pv, <2>d1, <1>nat
    <2>ss. /\ aux_stack' \in Seq(Nat)
           /\ Len(aux_stack') = Len(path) - 1
           /\ \A i \in 1..(Len(path) - 1) :
                  aux_stack'[i] = aux_stack[i]
        <3>1. /\ SubSeq(aux_stack, 1, Len(path) - 1) \in Seq(Nat)
              /\ Len(SubSeq(aux_stack, 1, Len(path) - 1)) =
                     (IF 1 <= Len(path) - 1
                      THEN (Len(path) - 1) - 1 + 1
                      ELSE 0)
              /\ \A i \in 1..(Len(path) - 1) - 1 + 1 :
                     SubSeq(aux_stack, 1, Len(path) - 1)[i] =
                     aux_stack[1 + i - 1]
            BY <2>ssub, <1>nat, SubSeqProperties
        <3> QED BY <3>1, <2>sv, <2>d1, <1>nat
    <2>1. TypeInvariant'
        <3>1. path' \in Seq(1..BranchFactor) BY <2>sp
        <3>2. Len(path') <= MaxDepth
            BY <2>sp, <2>d1, <1>nat, MaxDepthType
        <3>3. aux' \in Nat BY <2>av, <2>d1, <1>nat
        <3>4. aux_stack' \in Seq(Nat) BY <2>ss
        <3>5. Len(aux_stack') = Len(path') BY <2>sp, <2>ss
        <3>6. visited' \subseteq Seq(1..BranchFactor)
            BY <2>uv DEF TypeInvariant
        <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
            DEF TypeInvariant
    <2>2. DepthCoupling'
        <3>1. Len(path) \in 1..Len(path) BY <2>d1, <1>nat
        <3>2. aux_stack[Len(path)] = InitAux + (Len(path) - 1)
            BY <3>1 DEF DerivedStack
        <3> QED BY <2>av, <2>sp, <3>2, <1>nat, InitAuxType
            DEF DepthCoupling
    <2>3. DerivedStack'
        <3> SUFFICES ASSUME NEW i \in 1..Len(path')
                     PROVE aux_stack'[i] = InitAux + (i - 1)
            BY <2>sp DEF DerivedStack
        <3>1. i \in 1..(Len(path) - 1) BY <2>sp, <1>nat
        <3>2. aux_stack'[i] = aux_stack[i] BY <3>1, <2>ss
        <3>3. aux_stack[i] = InitAux + (i - 1)
            BY <3>1, <2>d1, <1>nat DEF DerivedStack
        <3> QED BY <3>2, <3>3
    <2>4. RecordedLeavesValid'
        BY <2>uv DEF RecordedLeavesValid
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv
<1>X. CASE Next
    BY <1>X, <1>1, <1>2, <1>3 DEF Next
<1> QED BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
<1>1. Init => Inv BY InitInv
<1>2. Inv /\ [Next]_vars => Inv' BY NextInv
<1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
    BY Safety, PTL DEF Inv
THEOREM DepthCouplingSafety == Spec => []DepthCoupling
    BY Safety, PTL DEF Inv
THEOREM DerivedStackSafety == Spec => []DerivedStack
    BY Safety, PTL DEF Inv
THEOREM RecordedLeavesSafety == Spec => []RecordedLeavesValid
    BY Safety, PTL DEF Inv
====
