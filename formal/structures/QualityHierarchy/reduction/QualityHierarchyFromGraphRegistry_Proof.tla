---- MODULE QualityHierarchyFromGraphRegistry_Proof ----
(* Parametric proof of Spec => QH!Spec for the graph-and-registry construction.

   UniqueOf makes each defaulted registry view deterministic. ViewUpsert maps
   ResourceRegistry insertion to a function EXCEPT update. UniqueParentOf,
   preserved by CAddChild's ~HasParent guard, makes the inverse-adjacency
   ParentView deterministic. The last property is construction-supplied;
   RelationshipGraph does not itself impose unique incoming parent edges. *)
EXTENDS QualityHierarchyFromGraphRegistry, FiniteSets, TLAPS

ASSUME MaxLevelType == MaxLevel \in Nat

\* Functional-form uniqueness and the defaulted view.

UniqueOf(S) == \A k \in Nodes : \A v1, v2 \in Vals :
                   (<<k, v1>> \in S /\ <<k, v2>> \in S) => v1 = v2

View(S) == [n \in Nodes |->
                IF \E v \in Vals : <<n, v>> \in S
                THEN CHOOSE v \in Vals : <<n, v>> \in S
                ELSE 0]

Upsert(S, k, v) == {e \in S : e[1] /= k} \cup {<<k, v>>}

LEMMA LevelIsView == LevelView = View(lvl_entries)
  BY DEF LevelView, View

LEMMA CostIsView == CostView = View(cost_entries)
  BY DEF CostView, View

LEMMA ViewEntry ==
  ASSUME NEW S, UniqueOf(S), NEW n \in Nodes, NEW v \in Vals, <<n, v>> \in S
  PROVE  View(S)[n] = v
  <1>ex. \E w \in Vals : <<n, w>> \in S
    OBVIOUS
  <1>ch. /\ (CHOOSE w \in Vals : <<n, w>> \in S) \in Vals
         /\ <<n, (CHOOSE w \in Vals : <<n, w>> \in S)>> \in S
    BY <1>ex
  <1>eq. (CHOOSE w \in Vals : <<n, w>> \in S) = v
    BY <1>ch DEF UniqueOf
  <1> QED  BY <1>ex, <1>eq DEF View

LEMMA ViewNoEntry ==
  ASSUME NEW S, NEW n \in Nodes, ~\E v \in Vals : <<n, v>> \in S
  PROVE  View(S)[n] = 0
  BY DEF View

LEMMA ViewEmpty == View({}) = [n \in Nodes |-> 0]
  <1>1. \A n \in Nodes : View({})[n] = 0
    BY ViewNoEntry
  <1> QED  BY <1>1 DEF View

\* Register upsert is an EXCEPT update of the derived view.

LEMMA UpsertPreservesUnique ==
  ASSUME NEW S, UniqueOf(S), NEW k \in Nodes, NEW v \in Vals
  PROVE  UniqueOf(Upsert(S, k, v))
  <1> SUFFICES ASSUME NEW key \in Nodes, NEW v1 \in Vals, NEW v2 \in Vals,
                      <<key, v1>> \in Upsert(S, k, v),
                      <<key, v2>> \in Upsert(S, k, v)
               PROVE  v1 = v2
    BY DEF UniqueOf
  <1>mem. \A w \in Vals : <<key, w>> \in Upsert(S, k, v) =>
              (key /= k /\ <<key, w>> \in S) \/ (key = k /\ w = v)
    BY DEF Upsert
  <1>A. CASE key = k   BY <1>A, <1>mem
  <1>B. CASE key /= k  BY <1>B, <1>mem DEF UniqueOf
  <1> QED  BY <1>A, <1>B

LEMMA ViewUpsert ==
  ASSUME NEW S, UniqueOf(S), NEW k \in Nodes, NEW v \in Vals
  PROVE  View(Upsert(S, k, v)) = [View(S) EXCEPT ![k] = v]
  <1>U. UniqueOf(Upsert(S, k, v))
    BY UpsertPreservesUnique
  <1>k. View(Upsert(S, k, v))[k] = v
    <2>1. <<k, v>> \in Upsert(S, k, v)  BY DEF Upsert
    <2> QED  BY <1>U, <2>1, ViewEntry
  <1>o. ASSUME NEW n \in Nodes, n /= k
        PROVE  View(Upsert(S, k, v))[n] = View(S)[n]
    <2>mem. \A w \in Vals : <<n, w>> \in Upsert(S, k, v) <=> <<n, w>> \in S
      BY <1>o DEF Upsert
    <2>A. CASE \E w \in Vals : <<n, w>> \in S
      <3>1. PICK w0 \in Vals : <<n, w0>> \in S  BY <2>A
      <3>2. View(S)[n] = w0                     BY <3>1, ViewEntry
      <3>3. <<n, w0>> \in Upsert(S, k, v)       BY <2>mem, <3>1
      <3>4. View(Upsert(S, k, v))[n] = w0       BY <1>U, <3>3, ViewEntry
      <3> QED  BY <3>2, <3>4
    <2>B. CASE ~\E w \in Vals : <<n, w>> \in S
      <3>1. ~\E w \in Vals : <<n, w>> \in Upsert(S, k, v)  BY <2>B, <2>mem
      <3>2. View(Upsert(S, k, v))[n] = 0                   BY <3>1, ViewNoEntry
      <3>3. View(S)[n] = 0                                 BY <2>B, ViewNoEntry
      <3> QED  BY <3>2, <3>3
    <2> QED  BY <2>A, <2>B
  <1>ptw. \A n \in Nodes :
            View(Upsert(S, k, v))[n] = [View(S) EXCEPT ![k] = v][n]
    <2>1. [View(S) EXCEPT ![k] = v][k] = v  BY DEF View
    <2>2. \A n \in Nodes : n /= k => [View(S) EXCEPT ![k] = v][n] = View(S)[n]
      BY DEF View
    <2> QED  BY <1>k, <1>o, <2>1, <2>2
  <1> QED  BY <1>ptw DEF View

\* Inverse-adjacency view. Unique parenthood is established by the construction
\* guard rather than by RelationshipGraph.

UniqueParentOf(A) == \A c \in Nodes : \A n1, n2 \in Nodes :
                         (c \in A[n1] /\ c \in A[n2]) => n1 = n2

PView(A) == [c \in Nodes |->
                IF \E n \in Nodes : c \in A[n]
                THEN CHOOSE n \in Nodes : c \in A[n]
                ELSE NULL]

LEMMA ParentIsPView == ParentView = PView(g_adjacency)
  BY DEF ParentView, PView, HasParent

\* Primed inverse-view equation used by action refinement.
LEMMA ParentPrimeIsPView == ParentView' = PView(g_adjacency')
  BY DEF ParentView, PView, HasParent

LEMMA ParentAt ==
  ASSUME NEW A, UniqueParentOf(A), NEW c \in Nodes, NEW n0 \in Nodes, c \in A[n0]
  PROVE  PView(A)[c] = n0
  <1>ex. \E n \in Nodes : c \in A[n]
    OBVIOUS
  <1>ch. /\ (CHOOSE n \in Nodes : c \in A[n]) \in Nodes
         /\ c \in A[CHOOSE n \in Nodes : c \in A[n]]
    BY <1>ex
  <1>eq. (CHOOSE n \in Nodes : c \in A[n]) = n0
    BY <1>ch DEF UniqueParentOf
  <1> QED  BY <1>ex, <1>eq DEF PView

LEMMA ParentNone ==
  ASSUME NEW A, NEW c \in Nodes, ~\E n \in Nodes : c \in A[n]
  PROVE  PView(A)[c] = NULL
  BY DEF PView

LEMMA ParentEmpty == PView([n \in Nodes |-> {}]) = [c \in Nodes |-> NULL]
  <1> DEFINE E == [n \in Nodes |-> {}]
  <1>1. \A c \in Nodes : PView(E)[c] = NULL
    <2> SUFFICES ASSUME NEW c \in Nodes PROVE PView(E)[c] = NULL  OBVIOUS
    <2>1. ~\E n \in Nodes : c \in E[n]  OBVIOUS
    <2> QED  BY <2>1, ParentNone
  <1> QED  BY <1>1 DEF PView

\* ---- The inductive invariant ---------------------------------------------

Inv ==
  /\ TypeInvariant
  /\ UniqueOf(lvl_entries)
  /\ UniqueOf(cost_entries)
  /\ UniqueParentOf(g_adjacency)

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>a. g_edges = {} /\ g_adjacency = [n \in Nodes |-> {}]
    BY DEF Init, RG!Init
  <1>l. lvl_entries = {}   BY DEF Init, LvlReg!Init
  <1>c. cost_entries = {}  BY DEF Init, CostReg!Init
  <1>1. TypeInvariant
    BY <1>a, <1>l, <1>c
       DEF TypeInvariant, RG!TypeInvariant, LvlReg!TypeInvariant,
           CostReg!TypeInvariant
  <1>2. UniqueOf(lvl_entries)         BY <1>l DEF UniqueOf
  <1>3. UniqueOf(cost_entries)        BY <1>c DEF UniqueOf
  <1>4. UniqueParentOf(g_adjacency)   BY <1>a DEF UniqueParentOf
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, RG!TypeInvariant, LvlReg!TypeInvariant,
              CostReg!TypeInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE \E p, c \in Nodes : CAddChild(p, c)
    <2> SUFFICES ASSUME NEW p \in Nodes, NEW c \in Nodes, CAddChild(p, c)
                 PROVE Inv'  BY <1>A
    <2>ne. p /= c                                          BY DEF CAddChild, RG!AddEdge
    <2>ed. g_edges' = g_edges \cup {<<p, c, 0>>}            BY DEF CAddChild, RG!AddEdge
    <2>ad. g_adjacency' = [g_adjacency EXCEPT ![p] = @ \cup {c}]
      BY DEF CAddChild, RG!AddEdge
    <2>un. lvl_entries' = lvl_entries /\ cost_entries' = cost_entries
      BY DEF CAddChild
    <2>np. ~\E n \in Nodes : c \in g_adjacency[n]           BY DEF CAddChild, HasParent
    <2>adom. g_adjacency \in [Nodes -> SUBSET Nodes]        OBVIOUS
    <2>pt. \A n \in Nodes : g_adjacency'[n] =
                              (IF n = p THEN g_adjacency[p] \cup {c} ELSE g_adjacency[n])
      BY <2>ad, <2>adom
    <2>1. TypeInvariant'
      <3>1. g_edges' \subseteq (Nodes \X Nodes \X (0..0))
        BY <2>ed DEF RG!TypeInvariant
      <3>2. g_adjacency' \in [Nodes -> SUBSET Nodes]
        \* From the EXCEPT itself, not pointwise: pointwise equality says
        \* nothing about the DOMAIN.
        BY <2>ad, <2>adom
      <3> QED  BY <3>1, <3>2, <2>un
                  DEF TypeInvariant, RG!TypeInvariant, LvlReg!TypeInvariant,
                      CostReg!TypeInvariant
    <2>2. UniqueOf(lvl_entries)'   BY <2>un DEF UniqueOf
    <2>3. UniqueOf(cost_entries)'  BY <2>un DEF UniqueOf
    <2>4. UniqueParentOf(g_adjacency)'
      <3> SUFFICES ASSUME NEW x \in Nodes, NEW n1 \in Nodes, NEW n2 \in Nodes,
                          x \in g_adjacency'[n1], x \in g_adjacency'[n2]
                   PROVE  n1 = n2
        BY DEF UniqueParentOf
      <3>1. \A n \in Nodes : x \in g_adjacency'[n] =>
                (x \in g_adjacency[n] \/ (n = p /\ x = c))
        BY <2>pt
      <3>A. CASE x = c
        \* Only p holds c after the step: nobody held it before.
        <4>1. \A n \in Nodes : x \in g_adjacency'[n] => n = p
          BY <3>1, <3>A, <2>np
        <4> QED  BY <4>1
      <3>B. CASE x /= c
        <4>1. \A n \in Nodes : x \in g_adjacency'[n] => x \in g_adjacency[n]
          BY <3>1, <3>B
        <4> QED  BY <4>1 DEF UniqueParentOf
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  <1>B. CASE \E n \in Nodes, l \in Vals, cc \in Vals : CSetNodeProperties(n, l, cc)
    <2> SUFFICES ASSUME NEW n \in Nodes, NEW l \in Vals, NEW cc \in Vals,
                        CSetNodeProperties(n, l, cc)
                 PROVE Inv'  BY <1>B
    <2>lv. lvl_entries' = Upsert(lvl_entries, n, l)
      BY DEF CSetNodeProperties, LvlReg!Register, Upsert
    <2>cv. cost_entries' = Upsert(cost_entries, n, cc)
      BY DEF CSetNodeProperties, CostReg!Register, Upsert
    <2>gr. g_edges' = g_edges /\ g_adjacency' = g_adjacency
      BY DEF CSetNodeProperties
    <2>1. TypeInvariant'
      <3>1. lvl_entries' \subseteq (Nodes \X Vals)
        BY <2>lv DEF Upsert, LvlReg!TypeInvariant
      <3>2. cost_entries' \subseteq (Nodes \X Vals)
        BY <2>cv DEF Upsert, CostReg!TypeInvariant
      <3> QED  BY <3>1, <3>2, <2>gr
                  DEF TypeInvariant, RG!TypeInvariant, LvlReg!TypeInvariant,
                      CostReg!TypeInvariant
    <2>2. UniqueOf(lvl_entries)'   BY <2>lv, UpsertPreservesUnique
    <2>3. UniqueOf(cost_entries)'  BY <2>cv, UpsertPreservesUnique
    <2>4. UniqueParentOf(g_adjacency)'  BY <2>gr DEF UniqueParentOf
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>X

\* ---- The refinement ------------------------------------------------------

LEMMA InitRefines == Init => QH!Init
  <1> SUFFICES ASSUME Init PROVE QH!Init  OBVIOUS
  <1>a. g_adjacency = [n \in Nodes |-> {}]  BY DEF Init, RG!Init
  <1>l. lvl_entries = {}                     BY DEF Init, LvlReg!Init
  <1>c. cost_entries = {}                    BY DEF Init, CostReg!Init
  <1>1. LevelView = [n \in Nodes |-> 0]
    BY <1>l, LevelIsView, ViewEmpty
  <1>2. CostView = [n \in Nodes |-> 0]
    BY <1>c, CostIsView, ViewEmpty
  <1>3. ChildrenView = [n \in Nodes |-> {}]
    BY <1>a DEF ChildrenView
  <1>4. ParentView = [c \in Nodes |-> NULL]
    BY <1>a, ParentIsPView, ParentEmpty
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF QH!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [QH!Next]_(QH!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [QH!Next]_(QH!vars)  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, RG!TypeInvariant, LvlReg!TypeInvariant,
              CostReg!TypeInvariant
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED QH!vars
      BY <1>0 DEF vars, QH!vars, LevelView, CostView, ChildrenView, ParentView,
                  HasParent
    <2> QED  BY <2>1
  <1>A. CASE \E p, c \in Nodes : CAddChild(p, c)
    <2> SUFFICES ASSUME NEW p \in Nodes, NEW c \in Nodes, CAddChild(p, c)
                 PROVE QH!AddChild(p, c)  BY <1>A DEF QH!Next
    <2>ne. p /= c                                    BY DEF CAddChild, RG!AddEdge
    <2>ad. g_adjacency' = [g_adjacency EXCEPT ![p] = @ \cup {c}]
      BY DEF CAddChild, RG!AddEdge
    <2>un. lvl_entries' = lvl_entries /\ cost_entries' = cost_entries
      BY DEF CAddChild
    <2>np. ~\E n \in Nodes : c \in g_adjacency[n]     BY DEF CAddChild, HasParent
    <2>adom. g_adjacency \in [Nodes -> SUBSET Nodes]  OBVIOUS
    <2>pt. \A n \in Nodes : g_adjacency'[n] =
                              (IF n = p THEN g_adjacency[p] \cup {c} ELSE g_adjacency[n])
      BY <2>ad, <2>adom
    <2>up. UniqueParentOf(g_adjacency)'
      BY NextInv, <1>A DEF Inv
    \* --- the four target conjuncts ---
    <2>1. c \notin ChildrenView[p]                   BY DEF CAddChild
    <2>2. ParentView[c] = NULL
      BY <2>np, ParentIsPView, ParentNone
    <2>3. LevelView[p] > LevelView[c] /\ CostView[p] <= CostView[c]
      BY DEF CAddChild
    <2>4. ChildrenView' = [ChildrenView EXCEPT ![p] = @ \cup {c}]
      BY <2>ad DEF ChildrenView
    <2>5. ParentView' = [ParentView EXCEPT ![c] = p]
      <3>c. ParentView'[c] = p
        <4>1. c \in g_adjacency'[p]  BY <2>pt
        <4> QED  BY <4>1, <2>up, ParentPrimeIsPView, ParentAt
      <3>o. ASSUME NEW x \in Nodes, x /= c PROVE ParentView'[x] = ParentView[x]
        <4>same. \A n \in Nodes : x \in g_adjacency'[n] <=> x \in g_adjacency[n]
          BY <2>pt, <3>o
        <4>A. CASE \E n \in Nodes : x \in g_adjacency[n]
          <5>1. PICK n0 \in Nodes : x \in g_adjacency[n0]  BY <4>A
          <5>2. ParentView[x] = n0
            BY <5>1, ParentIsPView, ParentAt DEF Inv
          <5>3. x \in g_adjacency'[n0]                     BY <4>same, <5>1
          <5>4. ParentView'[x] = n0
            BY <5>3, <2>up, ParentPrimeIsPView, ParentAt
          <5> QED  BY <5>2, <5>4
        <4>B. CASE ~\E n \in Nodes : x \in g_adjacency[n]
          <5>1. ~\E n \in Nodes : x \in g_adjacency'[n]  BY <4>B, <4>same
          <5>2. ParentView'[x] = NULL  BY <5>1, ParentPrimeIsPView, ParentNone
          <5>3. ParentView[x] = NULL   BY <4>B, ParentIsPView, ParentNone
          <5> QED  BY <5>2, <5>3
        <4> QED  BY <4>A, <4>B
      <3>ptw. \A x \in Nodes : ParentView'[x] = [ParentView EXCEPT ![c] = p][x]
        <4>1. [ParentView EXCEPT ![c] = p][c] = p  BY DEF ParentView
        <4>2. \A x \in Nodes : x /= c =>
                  [ParentView EXCEPT ![c] = p][x] = ParentView[x]
          BY DEF ParentView
        <4> QED  BY <3>c, <3>o, <4>1, <4>2
      <3> QED  BY <3>ptw DEF ParentView
    <2>6. LevelView' = LevelView /\ CostView' = CostView
      BY <2>un DEF LevelView, CostView
    <2> QED  BY <2>ne, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF QH!AddChild
  <1>B. CASE \E n \in Nodes, l \in Vals, cc \in Vals : CSetNodeProperties(n, l, cc)
    <2> SUFFICES ASSUME NEW n \in Nodes, NEW l \in Vals, NEW cc \in Vals,
                        CSetNodeProperties(n, l, cc)
                 PROVE QH!SetNodeProperties(n, l, cc)
      \* DEF Vals: the construction quantifies over Vals, the target over
      \* 0..MaxLevel, and they are the same set by definition.
      BY <1>B DEF QH!Next, Vals
    <2>lv. lvl_entries' = Upsert(lvl_entries, n, l)
      BY DEF CSetNodeProperties, LvlReg!Register, Upsert
    <2>cv. cost_entries' = Upsert(cost_entries, n, cc)
      BY DEF CSetNodeProperties, CostReg!Register, Upsert
    <2>gr. g_edges' = g_edges /\ g_adjacency' = g_adjacency
      BY DEF CSetNodeProperties
    <2>1. ChildrenView[n] = {}                       BY DEF CSetNodeProperties
    <2>2. ParentView[n] = NULL
      <3>1. ~\E m \in Nodes : n \in g_adjacency[m]   BY DEF CSetNodeProperties, HasParent
      <3> QED  BY <3>1, ParentIsPView, ParentNone
    <2>3. LevelView' = [LevelView EXCEPT ![n] = l]
      <3>1. UniqueOf(lvl_entries)                    BY DEF Inv
      <3>2. View(lvl_entries') = [View(lvl_entries) EXCEPT ![n] = l]
        BY <2>lv, <3>1, ViewUpsert
      <3> QED  BY <3>2, LevelIsView DEF LevelView, View
    <2>4. CostView' = [CostView EXCEPT ![n] = cc]
      <3>1. UniqueOf(cost_entries)                   BY DEF Inv
      <3>2. View(cost_entries') = [View(cost_entries) EXCEPT ![n] = cc]
        BY <2>cv, <3>1, ViewUpsert
      <3> QED  BY <3>2, CostIsView DEF CostView, View
    <2>5. ChildrenView' = ChildrenView /\ ParentView' = ParentView
      BY <2>gr DEF ChildrenView, ParentView, HasParent
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF QH!SetNodeProperties
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Refinement == Spec => QH!Spec
  <1>1. Init => Inv /\ QH!Init                       BY InitInv, InitRefines
  <1>2. Inv /\ [Next]_vars => Inv'                   BY NextInv
  <1>3. Inv /\ [Next]_vars => [QH!Next]_(QH!vars)    BY NextRefines
  <1> QED  BY <1>1, <1>2, <1>3, PTL DEF Spec, QH!Spec
====
