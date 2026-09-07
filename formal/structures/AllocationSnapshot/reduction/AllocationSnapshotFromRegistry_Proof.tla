---- MODULE AllocationSnapshotFromRegistry_Proof ----
(***************************************************************************
  Parametric TLAPS proof that the ResourceRegistry + Budget construction
  refines AllocationSnapshot:

      Refinement == Spec => AS!Spec

  It also proves TypeSafety, BudgetSafetySafety, and RegistryUniqueSafety.
  InvU is the functional-form strengthening used to derive the registry's
  Cardinality-form uniqueness. Nodes is arbitrary and BudgetCapacity may be
  any natural number, including zero. The construction adds no held glue
  state; MapAccepted, allocated, and capacity - allocated are projections.
 ***************************************************************************)
EXTENDS AllocationSnapshotFromRegistry, FiniteSetTheorems, TLAPS

ASSUME BudgetCapacityAss == BudgetCapacity \in Nat

\* Functional-form uniqueness: at most one cost per registered node. This is
\* the inductive strengthening behind RegistryUnique's Cardinality form.
InvU ==
    \A k \in Nodes : \A v1, v2 \in CostValues :
        (<<k, v1>> \in entries /\ <<k, v2>> \in entries) => v1 = v2

Inv == TypeInvariant /\ InvU

\* Init establishes the inductive invariant.
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY BudgetCapacityAss DEF Init, TypeInvariant
  <1>2. InvU
    BY DEF Init, InvU
  <1> QED BY <1>1, <1>2 DEF Inv

\* Every Next step preserves the inductive invariant.
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>c. /\ entries \subseteq (Nodes \X CostValues)
        /\ capacity = BudgetCapacity
        /\ allocated \in 0..BudgetCapacity
        /\ reserved = 0
        /\ pending_eviction = 0
        /\ InvU
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>c DEF Inv, vars, TypeInvariant, InvU
  <1>1. CASE Next
    <2> SUFFICES ASSUME NEW n \in Nodes, NEW c \in CostValues, AcceptNode(n, c)
                 PROVE Inv'
      BY <1>1 DEF Next
    <2>a. /\ ~\E v \in CostValues : <<n, v>> \in entries
          /\ allocated + reserved + pending_eviction + c <= capacity
          /\ entries' = {e \in entries : e[1] /= n} \cup {<<n, c>>}
          /\ allocated' = allocated + c
          /\ UNCHANGED <<capacity, reserved, pending_eviction>>
      BY DEF AcceptNode
    <2>t. c \in Nat /\ c >= 1 /\ allocated \in Nat
      BY <1>c, BudgetCapacityAss DEF CostValues
    <2>1. TypeInvariant'
      <3>1. entries' \subseteq (Nodes \X CostValues)
        BY <2>a, <1>c
      <3>2. allocated' \in 0..BudgetCapacity
        BY <2>a, <2>t, <1>c, BudgetCapacityAss
      <3> QED BY <3>1, <3>2, <2>a, <1>c DEF TypeInvariant
    <2>2. InvU'
      <3> SUFFICES ASSUME NEW k \in Nodes, NEW v1 \in CostValues,
                          NEW v2 \in CostValues,
                          <<k, v1>> \in entries', <<k, v2>> \in entries'
                   PROVE  v1 = v2
        BY DEF InvU
      <3>1. \A v \in CostValues :
                <<k, v>> \in entries' =>
                    (<<k, v>> \in entries /\ k /= n) \/ (k = n /\ v = c)
        BY <2>a
      <3>2. CASE k = n
        BY <3>1, <3>2
      <3>3. CASE k /= n
        BY <3>1, <3>3, <1>c DEF InvU
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>1, <2>2 DEF Inv
  <1> QED BY <1>0, <1>1

\* The inductive invariant holds in every reachable state.
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM BudgetSafetySafety == Spec => []BudgetSafety
  <1>1. Inv => BudgetSafety
    BY BudgetCapacityAss
       DEF Inv, TypeInvariant, BudgetSafety, Budget!SafetyInvariant
  <1> QED BY Safety, <1>1, PTL

\* Registry uniqueness follows because the matching-cost set for each key is
\* empty or a singleton. CardinalityBridge connects the instance-qualified
\* closed operator to this module's identical Cardinality term.
LEMMA CardinalityBridge == \A T : RR!Cardinality(T) = Cardinality(T)
  BY DEF RR!Cardinality, Cardinality

THEOREM RegistryUniqueSafety == Spec => []RegistryUnique
  <1>1. Inv => RegistryUnique
    <2> SUFFICES ASSUME Inv, NEW k \in Nodes
                 PROVE  RR!Cardinality({v \in CostValues : <<k, v>> \in entries}) <= 1
      BY DEF RegistryUnique, RR!UniqueMapping
    <2> DEFINE S == {v \in CostValues : <<k, v>> \in entries}
    <2>e. RR!Cardinality(S) = Cardinality(S)
      BY CardinalityBridge
    <2>f. IsFiniteSet(S)
      <3>1. IsFiniteSet(CostValues)
        BY BudgetCapacityAss, FS_Interval DEF CostValues
      <3>2. S \in SUBSET CostValues
        OBVIOUS
      <3> QED BY <3>1, <3>2, FS_Subset
    <2>n. Cardinality(S) \in Nat
      BY <2>f, FS_CardinalityType
    <2>1. CASE S = {}
      \* A finite empty set has cardinality zero.
      <3>1. Cardinality(S) = 0
        BY <2>1, <2>f, FS_EmptySet
      <3> QED BY <3>1, <2>e
    <2>2. CASE S /= {}
      \* InvU makes a nonempty S a singleton, hence its cardinality is one.
      <3>1. PICK v0 \in S : TRUE
        BY <2>2
      <3>2. \A v \in S : v = v0
        BY <3>1 DEF Inv, InvU
      <3>3. S = {v0}
        BY <3>1, <3>2
      <3>4. Cardinality(S) = 1
        BY <3>3, <2>f, FS_Singleton
      <3> QED BY <3>4, <2>e
    <2> QED BY <2>1, <2>2
  <1> QED BY Safety, <1>1, PTL

\* Init maps to AS!Init; every source step maps to an AS step or AS stutter.
LEMMA InitRefines == Init => AS!Init
  <1> SUFFICES ASSUME Init PROVE AS!Init
    OBVIOUS
  <1>1. MapAccepted = {}
    BY DEF Init, MapAccepted
  <1>2. allocated = 0
    BY DEF Init
  <1>3. capacity - allocated = BudgetCapacity
    BY BudgetCapacityAss DEF Init
  <1> QED BY <1>1, <1>2, <1>3 DEF AS!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [AS!Next]_(AS!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [AS!Next]_(AS!vars)
    OBVIOUS
  <1>c. /\ entries \subseteq (Nodes \X CostValues)
        /\ capacity = BudgetCapacity
        /\ allocated \in 0..BudgetCapacity
        /\ reserved = 0
        /\ pending_eviction = 0
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<MapAccepted, allocated, capacity - allocated>>
      BY <1>0 DEF vars, MapAccepted
    <2> QED BY <2>1 DEF AS!vars
  <1>1. CASE Next
    <2> SUFFICES ASSUME NEW n \in Nodes, NEW c \in CostValues, AcceptNode(n, c)
                 PROVE  [AS!Next]_(AS!vars)
      BY <1>1 DEF Next
    <2>a. /\ ~\E v \in CostValues : <<n, v>> \in entries
          /\ allocated + reserved + pending_eviction + c <= capacity
          /\ entries' = {e \in entries : e[1] /= n} \cup {<<n, c>>}
          /\ allocated' = allocated + c
          /\ UNCHANGED <<capacity, reserved, pending_eviction>>
      BY DEF AcceptNode
    <2>t. c \in Nat /\ c >= 1 /\ allocated \in Nat /\ capacity \in Nat
      BY <1>c, BudgetCapacityAss DEF CostValues
    <2>1. n \notin MapAccepted
      BY <2>a DEF MapAccepted
    <2>2. c <= capacity - allocated
      BY <2>a, <2>t, <1>c
    <2>3. MapAccepted' = MapAccepted \cup {n}
      <3>1. \A k \in Nodes :
                (\E v \in CostValues : <<k, v>> \in entries')
                    <=> (k = n \/ \E v \in CostValues : <<k, v>> \in entries)
        BY <2>a
      <3> QED BY <3>1 DEF MapAccepted
    <2>4. allocated' = allocated + c
      BY <2>a
    <2>5. capacity' - allocated' = (capacity - allocated) - c
      BY <2>a, <2>t, <1>c
    <2>6. AS!AcceptNode(n, c)
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF AS!AcceptNode
    <2>7. c \in 1..BudgetCapacity
      BY DEF CostValues
    <2> QED BY <2>6, <2>7 DEF AS!Next
  <1> QED BY <1>0, <1>1

\* The construction refines AllocationSnapshot.
THEOREM Refinement == Spec => AS!Spec
  <1>1. Init => AS!Init
    BY InitRefines
  <1>2. Inv /\ [Next]_vars => [AS!Next]_(AS!vars)
    BY NextRefines
  <1>3. Spec => []Inv
    BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, AS!Spec

\* Restatement using the carrier's refinement operator.
THEOREM RefinementOriginal == Spec => ASRefinement
  BY Refinement DEF ASRefinement

====
