---- MODULE BacktrackingTraversalUndo_Proof ----
(* TLAPS proof of BacktrackingTraversalUndo safety: TypeInvariant, Pairing,
   StateRestoration, and RecordedLeafValidity.

   The state machine descends an implicit decision tree (Descend pushes an
   UNDO TOKEN recording the pre-descent aux and the chosen delta, and applies
   the mutation), records leaves (Visit), and ascends (Ascend applies the
   recorded inverse and pops both stacks).

   The paired-undo discipline is carried by two co-dependent invariants over
   held restoration content:

     Pairing          : one ledger entry per outstanding descent, and
                        aux = Mutate(head.saved, head.delta)
     StateRestoration : the ledger is a well-formed chain -- entry 1 saves
                        InitAux, and entry i saves entry (i-1)'s mutation

   Pairing's Ascend case needs StateRestoration (the popped entry's saved
   value is exactly the mutation of its predecessor, or InitAux at depth 1);
   StateRestoration's Descend case needs Pairing (the pushed saved value is
   the live aux, which Pairing says is the previous head's mutation).  Both
   live in Inv so each witnesses the other. RecordedLeafValidity depends on
   TypeInvariant.

   Mutate and Undo are constant operators. The proof uses only closure and the
   round-trip law, independent of the TLC instance.                            *)
EXTENDS BacktrackingTraversalUndo, Naturals, Sequences, SequenceTheorems, TLAPS

\* ---- Constant typing: the proof binds no constant to a value, only a type ---
ASSUME BranchFactorType == BranchFactor \in Nat
ASSUME MaxDepthType     == MaxDepth \in Nat
ASSUME InitAuxType      == InitAux \in AuxDomain

\* ---- The mutation contract: closure and the round-trip law ----------------
ASSUME MutateClosed ==
    \A v \in AuxDomain, d \in Deltas : Mutate(v, d) \in AuxDomain
ASSUME UndoInverts ==
    \A v \in AuxDomain, d \in Deltas : Undo(Mutate(v, d), d) = v

Inv ==
  /\ TypeInvariant
  /\ Pairing
  /\ StateRestoration
  /\ RecordedLeafValidity

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1> USE DEF Init, Depth
  <1>1. TypeInvariant
    BY MaxDepthType, InitAuxType DEF TypeInvariant
  <1>2. Pairing
    \* ledger = <<>> so Len(ledger) = 0 = Depth; the Depth > 0 branch is vacuous.
    BY InitAuxType DEF Pairing
  <1>3. StateRestoration
    \* Len(ledger) = 0: both conjuncts are vacuous (1..0 = {} and 2..0 = {}).
    BY DEF StateRestoration
  <1>4. RecordedLeafValidity
    \* visited = {}; vacuous.
    BY DEF RecordedLeafValidity
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, Pairing, StateRestoration,
              RecordedLeafValidity,
              Depth, IsLeaf, Token
  \* Common unprimed-state typings.  Len(ledger) = Len(path) comes from
  \* Pairing (it is obligation content here, not typing: "one entry per
  \* outstanding descent").
  <1>nat. /\ path \in Seq(1..BranchFactor)
          /\ ledger \in Seq(Token)
          /\ aux \in AuxDomain
          /\ Len(path) \in Nat
          /\ Len(ledger) \in Nat
          /\ Len(ledger) = Len(path)
          /\ Len(path) <= MaxDepth
          /\ path \in [1..Len(path) -> 1..BranchFactor]
          /\ ledger \in [1..Len(ledger) -> Token]
    BY LenProperties DEF TypeInvariant, Pairing
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  \* ---- Descend(c, d) ----------------------------------------------------
  <1>1. CASE \E c \in 1..BranchFactor, d \in Deltas : Descend(c, d)
    <2> SUFFICES ASSUME NEW c \in 1..BranchFactor, NEW d \in Deltas, Descend(c, d)
                 PROVE Inv'
      BY <1>1
    <2>tk. [saved |-> aux, delta |-> d] \in Token
      BY <1>nat DEF Token
    <2>nl. Len(path) # MaxDepth                            BY DEF Descend
    <2>pa. path' = Append(path, c)                         BY DEF Descend
    <2>la. ledger' = Append(ledger, [saved |-> aux, delta |-> d])  BY DEF Descend
    <2>aa. aux' = Mutate(aux, d)                           BY DEF Descend
    <2>va. visited' = visited                              BY DEF Descend
    \* Append facts for path (over 1..BranchFactor) and ledger (over Token).
    <2>ap. /\ path' \in Seq(1..BranchFactor)
           /\ Len(path') = Len(path) + 1
           /\ \A i \in 1..Len(path) : path'[i] = path[i]
           /\ path'[Len(path) + 1] = c
      BY <2>pa, <1>nat, AppendProperties
    <2>al. /\ ledger' \in Seq(Token)
           /\ Len(ledger') = Len(ledger) + 1
           /\ \A i \in 1..Len(ledger) : ledger'[i] = ledger[i]
           /\ ledger'[Len(ledger) + 1] = [saved |-> aux, delta |-> d]
      BY <2>la, <2>tk, <1>nat, AppendProperties
    <2>1. TypeInvariant'
      <3>1. path' \in Seq(1..BranchFactor)          BY <2>ap
      <3>2. Len(path') <= MaxDepth                  BY <2>ap, <2>nl, <1>nat, MaxDepthType
      <3>3. aux' \in AuxDomain                      BY <2>aa, <1>nat, MutateClosed
      <3>4. ledger' \in Seq(Token)                  BY <2>al
      <3>5. visited' \subseteq Seq(1..BranchFactor) BY <2>va DEF TypeInvariant
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF TypeInvariant
    <2>2. Pairing'
      <3>1. Len(ledger') = Len(path')               BY <2>ap, <2>al, <1>nat
      <3>2. Len(path') > 0                          BY <2>ap, <1>nat
      <3>3. ledger'[Len(path')] = [saved |-> aux, delta |-> d]
        BY <2>ap, <2>al, <1>nat
      <3> QED  BY <3>1, <3>2, <3>3, <2>aa DEF Pairing
    <2>3. StateRestoration'
      <3>1. Len(ledger') >= 1 => ledger'[1].saved = InitAux
        <4> SUFFICES ASSUME Len(ledger') >= 1 PROVE ledger'[1].saved = InitAux
          OBVIOUS
        <4>1. CASE Len(ledger) = 0
          \* ledger' = <<token>>; token.saved = aux = InitAux by Pairing at Depth 0.
          <5>1. ledger'[1] = [saved |-> aux, delta |-> d]  BY <4>1, <2>al
          <5>2. aux = InitAux                              BY <4>1, <1>nat DEF Pairing
          <5> QED  BY <5>1, <5>2
        <4>2. CASE Len(ledger) >= 1
          <5>1. ledger'[1] = ledger[1]                     BY <4>2, <2>al, <1>nat
          <5> QED  BY <5>1, <4>2 DEF StateRestoration
        <4> QED  BY <4>1, <4>2, <1>nat
      <3>2. \A i \in 2..Len(ledger') :
               ledger'[i].saved = Mutate(ledger'[i-1].saved, ledger'[i-1].delta)
        <4> SUFFICES ASSUME NEW i \in 2..Len(ledger')
                     PROVE ledger'[i].saved = Mutate(ledger'[i-1].saved, ledger'[i-1].delta)
          OBVIOUS
        <4>1. CASE i \in 2..Len(ledger)
          <5>1. i - 1 \in 1..Len(ledger)                   BY <4>1, <1>nat
          <5>2. ledger'[i] = ledger[i]                     BY <4>1, <2>al, <1>nat
          <5>3. ledger'[i-1] = ledger[i-1]                 BY <5>1, <2>al
          <5> QED  BY <5>2, <5>3, <4>1 DEF StateRestoration
        <4>2. CASE i = Len(ledger) + 1
          <5>1. Len(ledger) >= 1                           BY <4>2, <1>nat
          <5>2. ledger'[i] = [saved |-> aux, delta |-> d]  BY <4>2, <2>al
          <5>3. ledger'[i-1] = ledger[Len(ledger)]         BY <4>2, <5>1, <2>al, <1>nat
          <5>4. aux = Mutate(ledger[Len(path)].saved, ledger[Len(path)].delta)
            BY <5>1, <1>nat DEF Pairing
          <5> QED  BY <5>2, <5>3, <5>4, <1>nat
        <4> QED  BY <4>1, <4>2, <2>al, <1>nat
      <3> QED  BY <3>1, <3>2 DEF StateRestoration
    <2>4. RecordedLeafValidity'
      BY <2>va DEF RecordedLeafValidity
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  \* ---- Visit ------------------------------------------------------------
  <1>2. CASE Visit
    <2>leaf. Len(path) = MaxDepth                          BY <1>2 DEF Visit
    <2>vv. visited' = visited \cup {path}                  BY <1>2 DEF Visit
    <2>uc. path' = path /\ aux' = aux /\ ledger' = ledger  BY <1>2 DEF Visit
    <2>1. TypeInvariant'
      BY <2>uc, <2>vv, <1>nat DEF TypeInvariant
    <2>2. Pairing'
      BY <2>uc DEF Pairing
    <2>3. StateRestoration'
      BY <2>uc DEF StateRestoration
    <2>4. RecordedLeafValidity'
      <3> SUFFICES ASSUME NEW p \in visited'
                   PROVE  /\ Len(p) = MaxDepth
                          /\ \A i \in 1..MaxDepth : p[i] \in 1..BranchFactor
        BY DEF RecordedLeafValidity
      <3>1. CASE p \in visited
        BY <3>1 DEF RecordedLeafValidity
      <3>2. CASE p = path
        <4>1. Len(p) = MaxDepth                            BY <3>2, <2>leaf
        <4>2. \A i \in 1..MaxDepth : p[i] \in 1..BranchFactor
          BY <3>2, <2>leaf, <1>nat
        <4> QED  BY <4>1, <4>2
      <3> QED  BY <3>1, <3>2, <2>vv
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  \* ---- Ascend -----------------------------------------------------------
  <1>3. CASE Ascend
    <2>d1. Len(path) >= 1                                  BY <1>3 DEF Ascend
    <2>av. aux' = Undo(aux, ledger[Len(path)].delta)       BY <1>3 DEF Ascend
    <2>lv. ledger' = SubSeq(ledger, 1, Len(path) - 1)      BY <1>3 DEF Ascend
    <2>pv. path' = SubSeq(path, 1, Len(path) - 1)          BY <1>3 DEF Ascend
    <2>uv. visited' = visited                              BY <1>3 DEF Ascend
    \* The head token is well-typed, so its two fields are in their domains.
    <2>hd. /\ ledger[Len(path)] \in Token
           /\ ledger[Len(path)].saved \in AuxDomain
           /\ ledger[Len(path)].delta \in Deltas
      <3>1. Len(path) \in 1..Len(ledger)                   BY <2>d1, <1>nat
      <3> QED  BY <3>1, <1>nat DEF Token
    \* Pairing expresses aux as the head mutation; the round-trip law restores
    \* the head token's saved value.
    <2>rest. aux' = ledger[Len(path)].saved
      <3>1. aux = Mutate(ledger[Len(path)].saved, ledger[Len(path)].delta)
        BY <2>d1, <1>nat DEF Pairing
      <3> QED  BY <2>av, <3>1, <2>hd, UndoInverts
    \* SubSeq facts (m = 1, n = Len(path)-1; Len = Len(path)-1 since Len>=1).
    <2>psub. \A i \in 1..(Len(path) - 1) : path[i] \in 1..BranchFactor
      BY <1>nat
    <2>lsub. \A i \in 1..(Len(path) - 1) : ledger[i] \in Token
      BY <1>nat
    <2>sp. /\ path' \in Seq(1..BranchFactor)
           /\ Len(path') = Len(path) - 1
           /\ \A i \in 1..(Len(path) - 1) : path'[i] = path[i]
      <3>1. /\ SubSeq(path, 1, Len(path) - 1) \in Seq(1..BranchFactor)
            /\ Len(SubSeq(path, 1, Len(path) - 1)) = (IF 1 <= Len(path) - 1 THEN (Len(path) - 1) - 1 + 1 ELSE 0)
            /\ \A i \in 1..(Len(path) - 1) - 1 + 1 : SubSeq(path, 1, Len(path) - 1)[i] = path[1 + i - 1]
        BY <2>psub, <1>nat, SubSeqProperties
      <3> QED  BY <3>1, <2>pv, <2>d1, <1>nat
    <2>sl. /\ ledger' \in Seq(Token)
           /\ Len(ledger') = Len(path) - 1
           /\ \A i \in 1..(Len(path) - 1) : ledger'[i] = ledger[i]
      <3>1. /\ SubSeq(ledger, 1, Len(path) - 1) \in Seq(Token)
            /\ Len(SubSeq(ledger, 1, Len(path) - 1)) = (IF 1 <= Len(path) - 1 THEN (Len(path) - 1) - 1 + 1 ELSE 0)
            /\ \A i \in 1..(Len(path) - 1) - 1 + 1 : SubSeq(ledger, 1, Len(path) - 1)[i] = ledger[1 + i - 1]
        BY <2>lsub, <1>nat, SubSeqProperties
      <3> QED  BY <3>1, <2>lv, <2>d1, <1>nat
    <2>1. TypeInvariant'
      <3>1. path' \in Seq(1..BranchFactor)          BY <2>sp
      <3>2. Len(path') <= MaxDepth                  BY <2>sp, <2>d1, <1>nat, MaxDepthType
      <3>3. aux' \in AuxDomain                      BY <2>rest, <2>hd
      <3>4. ledger' \in Seq(Token)                  BY <2>sl
      <3>5. visited' \subseteq Seq(1..BranchFactor) BY <2>uv DEF TypeInvariant
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF TypeInvariant
    <2>2. Pairing'
      <3>1. Len(ledger') = Len(path')                      BY <2>sp, <2>sl
      <3>2. CASE Len(path) = 1
        \* Depth' = 0: the restored value is entry 1's saved, which is InitAux.
        <4>1. Len(path') = 0                               BY <3>2, <2>sp, <1>nat
        <4>2. Len(ledger) >= 1                             BY <2>d1, <1>nat
        <4>3. ledger[1].saved = InitAux                    BY <4>2 DEF StateRestoration
        <4>4. aux' = InitAux                               BY <2>rest, <3>2, <4>3
        <4> QED  BY <3>1, <4>1, <4>4 DEF Pairing
      <3>3. CASE Len(path) >= 2
        \* Depth' > 0: the restored value is the new head's mutation, which is
        \* exactly StateRestoration's chain link at i = Len(path).
        <4>1. Len(path') = Len(path) - 1                   BY <2>sp
        <4>2. Len(path') > 0                               BY <4>1, <3>3, <1>nat
        <4>3. Len(path) \in 2..Len(ledger)                 BY <3>3, <1>nat
        <4>4. ledger[Len(path)].saved
                = Mutate(ledger[Len(path)-1].saved, ledger[Len(path)-1].delta)
          BY <4>3 DEF StateRestoration
        <4>5. ledger'[Len(path')] = ledger[Len(path) - 1]  BY <4>1, <3>3, <2>sl, <1>nat
        <4> QED  BY <3>1, <4>2, <4>4, <4>5, <2>rest, <4>1 DEF Pairing
      <3> QED  BY <3>2, <3>3, <2>d1, <1>nat
    <2>3. StateRestoration'
      \* ledger' is a prefix of ledger, so both chain conditions carry over.
      <3>1. Len(ledger') >= 1 => ledger'[1].saved = InitAux
        <4> SUFFICES ASSUME Len(ledger') >= 1 PROVE ledger'[1].saved = InitAux
          OBVIOUS
        <4>1. Len(path) - 1 >= 1                           BY <2>sl, <1>nat, <2>d1
        <4>2. ledger'[1] = ledger[1]                       BY <4>1, <2>sl, <1>nat
        <4>3. Len(ledger) >= 1                             BY <2>d1, <1>nat
        <4> QED  BY <4>2, <4>3 DEF StateRestoration
      <3>2. \A i \in 2..Len(ledger') :
               ledger'[i].saved = Mutate(ledger'[i-1].saved, ledger'[i-1].delta)
        <4> SUFFICES ASSUME NEW i \in 2..Len(ledger')
                     PROVE ledger'[i].saved = Mutate(ledger'[i-1].saved, ledger'[i-1].delta)
          OBVIOUS
        <4>1. i \in 1..(Len(path) - 1)                     BY <2>sl, <1>nat
        <4>2. i - 1 \in 1..(Len(path) - 1)                 BY <4>1, <1>nat
        <4>3. ledger'[i] = ledger[i]                       BY <4>1, <2>sl
        <4>4. ledger'[i-1] = ledger[i-1]                   BY <4>2, <2>sl
        <4>5. i \in 2..Len(ledger)                         BY <4>1, <1>nat, <2>d1
        <4> QED  BY <4>3, <4>4, <4>5 DEF StateRestoration
      <3> QED  BY <3>1, <3>2 DEF StateRestoration
    <2>4. RecordedLeafValidity'
      BY <2>uv DEF RecordedLeafValidity
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  <1>X. CASE Next
    BY <1>X, <1>1, <1>2, <1>3 DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'   BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

\* Corollaries in the carrier's public invariant vocabulary.
THEOREM TypeSafety == Spec => []TypeInvariant                 BY Safety, PTL DEF Inv
THEOREM PairingSafety == Spec => []Pairing                    BY Safety, PTL DEF Inv
THEOREM StateRestorationSafety == Spec => []StateRestoration   BY Safety, PTL DEF Inv
THEOREM RecordedLeafValiditySafety == Spec => []RecordedLeafValidity
  BY Safety, PTL DEF Inv

THEOREM CompletenessSafety == Spec => []Completeness
  BY RecordedLeafValiditySafety, PTL DEF Completeness
====
