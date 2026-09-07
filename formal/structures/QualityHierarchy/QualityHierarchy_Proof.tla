---- MODULE QualityHierarchy_Proof ----
(* TLAPS proof of QualityHierarchy safety.
   StrictLevelDescent and ParentEdgeAgreement are co-dependent for
   inductiveness because SetNodeProperties uses parent[n] = NULL to
   conclude n is not in any children set. *)
EXTENDS QualityHierarchy, Naturals, FiniteSets, TLAPS

ASSUME MaxLevelType == MaxLevel \in Nat
ASSUME NotANode == NULL \notin Nodes

Inv == TypeInvariant /\ StrictLevelDescent /\ ParentEdgeAgreement /\ CostMonotonicity

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY MaxLevelType DEF Init, TypeInvariant
  <1>2. StrictLevelDescent
    BY DEF Init, StrictLevelDescent
  <1>3. ParentEdgeAgreement
    BY DEF Init, ParentEdgeAgreement
  <1>4. CostMonotonicity
    BY DEF Init, CostMonotonicity
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, StrictLevelDescent, ParentEdgeAgreement, CostMonotonicity
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE \E p, c \in Nodes : AddChild(p, c)
    <2> SUFFICES ASSUME NEW p \in Nodes, NEW c \in Nodes, AddChild(p, c)
                 PROVE Inv'
      BY <1>A
    <2>a. children' = [children EXCEPT ![p] = @ \cup {c}]    BY DEF AddChild
    <2>b. parent' = [parent EXCEPT ![c] = p]                 BY DEF AddChild
    <2>c. level' = level                                      BY DEF AddChild
    <2>d. cost' = cost                                        BY DEF AddChild
    <2>e. p /= c                                              BY DEF AddChild
    <2>f. c \notin children[p]                                BY DEF AddChild
    <2>g. parent[c] = NULL                                    BY DEF AddChild
    <2>h. level[p] > level[c]                                 BY DEF AddChild
    <2>1. TypeInvariant'
      <3>1. level' \in [Nodes -> 0..MaxLevel]   BY <2>c
      <3>2. cost' \in [Nodes -> Nat]            BY <2>d
      <3>3. children' \in [Nodes -> SUBSET Nodes]
        BY <2>a
      <3>4. parent' \in [Nodes -> Nodes \cup {NULL}]
        BY <2>b
      <3> QED  BY <3>1, <3>2, <3>3, <3>4
    <2>2. StrictLevelDescent'
      <3> SUFFICES ASSUME NEW n \in Nodes, NEW cc \in children'[n]
                   PROVE level'[n] > level'[cc]
        OBVIOUS
      <3>1. CASE n = p
        <4>1. children'[n] = children[p] \cup {c}    BY <2>a, <3>1
        <4>2. cc \in children[p] \/ cc = c           BY <4>1
        <4>3. CASE cc \in children[p]
          <5>1. level[p] > level[cc]    BY <4>3 DEF Inv, StrictLevelDescent
          <5> QED  BY <2>c, <3>1, <5>1
        <4>4. CASE cc = c
          <5> QED  BY <2>c, <2>h, <3>1, <4>4
        <4> QED  BY <4>2, <4>3, <4>4
      <3>2. CASE n /= p
        <4>1. children'[n] = children[n]    BY <2>a, <3>2
        <4>2. cc \in children[n]            BY <4>1
        <4>3. level[n] > level[cc]          BY <4>2 DEF Inv, StrictLevelDescent
        <4> QED  BY <2>c, <4>3
      <3> QED  BY <3>1, <3>2
    <2>3. ParentEdgeAgreement'
      <3> SUFFICES ASSUME NEW n \in Nodes, NEW cc \in children'[n]
                   PROVE parent'[cc] = n
        OBVIOUS
      <3>1. CASE n = p
        <4>1. children'[n] = children[p] \cup {c}    BY <2>a, <3>1
        <4>2. cc \in children[p] \/ cc = c           BY <4>1
        <4>3. CASE cc \in children[p]
          \* parent[cc] = p by IH; parent'[cc] = parent[cc] unless cc = c.
          \* If cc = c, contradicts <2>f (c notin children[p]).
          <5>1. cc /= c                BY <2>f, <4>3
          <5>2. parent'[cc] = parent[cc]   BY <2>b, <5>1
          <5>3. parent[cc] = p         BY <4>3 DEF Inv, ParentEdgeAgreement
          <5> QED  BY <3>1, <5>2, <5>3
        <4>4. CASE cc = c
          <5>1. parent'[cc] = p        BY <2>b, <4>4
          <5> QED  BY <3>1, <5>1
        <4> QED  BY <4>2, <4>3, <4>4
      <3>2. CASE n /= p
        <4>1. children'[n] = children[n]    BY <2>a, <3>2
        <4>2. cc \in children[n]            BY <4>1
        <4>3. parent[cc] = n                BY <4>2 DEF Inv, ParentEdgeAgreement
        \* parent[c] = NULL by <2>g; if cc = c, then n = parent[c] = NULL,
        \* contradicting n \in Nodes via NotANode.
        <4>4. cc /= c
          BY <2>g, <4>3, NotANode
        <4>5. parent'[cc] = parent[cc]      BY <2>b, <4>4
        <4> QED  BY <4>3, <4>5
      <3> QED  BY <3>1, <3>2
    <2>4. CostMonotonicity'
      <3> SUFFICES ASSUME NEW n \in Nodes, NEW cc \in children'[n]
                   PROVE cost'[n] <= cost'[cc]
        OBVIOUS
      <3>1. CASE n = p
        <4>1. children'[n] = children[p] \cup {c}    BY <2>a, <3>1
        <4>2. cc \in children[p] \/ cc = c           BY <4>1
        <4>3. CASE cc \in children[p]
          <5>1. cost[p] <= cost[cc]    BY <4>3 DEF Inv, CostMonotonicity
          <5> QED  BY <2>d, <3>1, <5>1
        <4>4. CASE cc = c
          <5>1. cost[p] <= cost[c]     BY DEF AddChild
          <5> QED  BY <2>d, <3>1, <4>4, <5>1
        <4> QED  BY <4>2, <4>3, <4>4
      <3>2. CASE n /= p
        <4>1. children'[n] = children[n]    BY <2>a, <3>2
        <4>2. cc \in children[n]            BY <4>1
        <4>3. cost[n] <= cost[cc]          BY <4>2 DEF Inv, CostMonotonicity
        <4> QED  BY <2>d, <4>3
      <3> QED  BY <3>1, <3>2
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>B. CASE \E n \in Nodes, l \in 0..MaxLevel, cc \in 0..MaxLevel : SetNodeProperties(n, l, cc)
    <2> SUFFICES ASSUME NEW n \in Nodes, NEW l \in 0..MaxLevel,
                         NEW cc \in 0..MaxLevel, SetNodeProperties(n, l, cc)
                 PROVE Inv'
      BY <1>B
    <2>a. children[n] = {}                                    BY DEF SetNodeProperties
    <2>b. parent[n] = NULL                                    BY DEF SetNodeProperties
    <2>c. level' = [level EXCEPT ![n] = l]                    BY DEF SetNodeProperties
    <2>d. cost' = [cost EXCEPT ![n] = cc]                     BY DEF SetNodeProperties
    <2>e. children' = children                                BY DEF SetNodeProperties
    <2>f. parent' = parent                                    BY DEF SetNodeProperties
    <2>1. TypeInvariant'
      <3>1. level' \in [Nodes -> 0..MaxLevel]   BY <2>c
      <3>2. cost' \in [Nodes -> Nat]            BY <2>d, MaxLevelType
      <3>3. children' \in [Nodes -> SUBSET Nodes]   BY <2>e
      <3>4. parent' \in [Nodes -> Nodes \cup {NULL}]   BY <2>f
      <3> QED  BY <3>1, <3>2, <3>3, <3>4
    <2>2. StrictLevelDescent'
      <3> SUFFICES ASSUME NEW m \in Nodes, NEW c2 \in children'[m]
                   PROVE level'[m] > level'[c2]
        OBVIOUS
      <3>1. c2 \in children[m]      BY <2>e
      \* c2 cannot be n: if c2 = n, then parent[c2] = m by IH ParentEdgeAgreement,
      \* but parent[n] = NULL by <2>b, so m = NULL, contradicting NotANode.
      <3>2. parent[c2] = m          BY <3>1 DEF Inv, ParentEdgeAgreement
      <3>3. c2 /= n                 BY <2>b, <3>2, NotANode
      <3>4. level'[c2] = level[c2]  BY <2>c, <3>3
      \* Similarly m /= n: if m = n, children[n] = {} by <2>a, but c2 \in children[m] = {}.
      <3>5. m /= n
        BY <2>a, <3>1
      <3>6. level'[m] = level[m]    BY <2>c, <3>5
      <3>7. level[m] > level[c2]    BY <3>1 DEF Inv, StrictLevelDescent
      <3> QED  BY <3>4, <3>6, <3>7
    <2>3. ParentEdgeAgreement'
      <3> SUFFICES ASSUME NEW m \in Nodes, NEW c2 \in children'[m]
                   PROVE parent'[c2] = m
        OBVIOUS
      <3>1. c2 \in children[m]      BY <2>e
      <3>2. parent[c2] = m          BY <3>1 DEF Inv, ParentEdgeAgreement
      <3> QED  BY <2>f, <3>2
    <2>4. CostMonotonicity'
      <3> SUFFICES ASSUME NEW m \in Nodes, NEW c2 \in children'[m]
                   PROVE cost'[m] <= cost'[c2]
        OBVIOUS
      <3>1. c2 \in children[m]      BY <2>e
      <3>2. parent[c2] = m          BY <3>1 DEF Inv, ParentEdgeAgreement
      <3>3. c2 /= n                 BY <2>b, <3>2, NotANode
      <3>4. cost'[c2] = cost[c2]    BY <2>d, <3>3
      <3>5. m /= n                  BY <2>a, <3>1
      <3>6. cost'[m] = cost[m]      BY <2>d, <3>5
      <3>7. cost[m] <= cost[c2]     BY <3>1 DEF Inv, CostMonotonicity
      <3> QED  BY <3>4, <3>6, <3>7
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant     BY Safety, PTL DEF Inv
THEOREM StrictLevelDescentSafety == Spec => []StrictLevelDescent  BY Safety, PTL DEF Inv
THEOREM ParentEdgeAgreementSafety == Spec => []ParentEdgeAgreement  BY Safety, PTL DEF Inv
THEOREM CostMonotonicitySafety == Spec => []CostMonotonicity  BY Safety, PTL DEF Inv
====
