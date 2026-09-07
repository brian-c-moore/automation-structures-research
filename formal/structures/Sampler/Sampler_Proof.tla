---- MODULE Sampler_Proof ----
(* TLAPS safety proof for Sampler.

   Inv is TypeInvariant /\ BoundedSample /\ SupportConsistency -- the two
   advertised obligations plus typing. The draw case proves the fused
   read-and-select action. The writer case is short: `Zero` cannot touch a selected
   item's weight, so SupportConsistency's witness for a selected s is the
   same value it was.

   Contracts: SampleSizeType, ItemsFinite, and MaxProbType.                 *)
EXTENDS Sampler, Naturals, FiniteSets, FiniteSetTheorems, TLAPS

ASSUME SampleSizeType == SampleSize \in Nat
ASSUME ItemsFinite == IsFiniteSet(Items)
ASSUME MaxProbType == MaxProb \in Nat

Inv == TypeInvariant /\ BoundedSample /\ SupportConsistency

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant     BY MaxProbType DEF Init, TypeInvariant
  <1>2. BoundedSample
    <2>1. Cardinality({}) = 0   BY FS_EmptySet
    <2>2. selected = {}          BY DEF Init
    <2>3. Cardinality(selected) = 0  BY <2>1, <2>2
    <2> QED  BY <2>3, SampleSizeType DEF BoundedSample
  <1>3. SupportConsistency
    BY DEF Init, SupportConsistency
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BoundedSample, SupportConsistency

  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars

  \* ---- the draw: the distribution read and the selection, fused ----
  <1>1. ASSUME Sample PROVE Inv'
    <2>1. Cardinality(selected) < SampleSize  BY <1>1 DEF Sample
    <2>2. \E i \in Items : /\ distribution[i] > 0
                           /\ selected' = selected \cup {i}
                           /\ UNCHANGED distribution
      BY <1>1 DEF Sample
    <2> SUFFICES ASSUME NEW i \in Items,
                        distribution[i] > 0,
                        selected' = selected \cup {i},
                        UNCHANGED distribution
                 PROVE Inv'
      BY <2>2
    <2>a. selected \subseteq Items                       OBVIOUS
    <2>b. IsFiniteSet(selected)
      BY <2>a, FS_Subset, ItemsFinite
    <2>3. selected' \subseteq Items                       BY <2>a
    <2>4. distribution' \in [Items -> 0..MaxProb]         OBVIOUS
    <2>9. Cardinality(selected) \in Nat
      BY <2>b, FS_CardinalityType
    <2>9a. selected' = selected \cup {i}    OBVIOUS
    <2>9b. IsFiniteSet(selected')
      BY <2>b, <2>9a, FS_AddElement
    <2>9c. Cardinality(selected') \in Nat
      BY <2>9b, FS_CardinalityType
    <2>5. Cardinality(selected') <= Cardinality(selected) + 1
      <3>2. Cardinality(selected \cup {i})
              = IF i \in selected THEN Cardinality(selected) ELSE Cardinality(selected) + 1
        BY <2>b, FS_AddElement
      <3>3. Cardinality(selected \cup {i}) <= Cardinality(selected) + 1
        BY <2>9, <3>2
      <3> QED  BY <2>9a, <3>3
    <2>6. Cardinality(selected) + 1 <= SampleSize
      BY <2>1, <2>9, SampleSizeType
    <2>7. Cardinality(selected') <= SampleSize
      BY <2>5, <2>6, <2>9, <2>9c, SampleSizeType
    <2>8. SupportConsistency'
      <3> SUFFICES ASSUME NEW s \in selected' PROVE distribution'[s] > 0
        BY DEF SupportConsistency
      <3>1. s \in selected \/ s = i                        OBVIOUS
      <3> QED  BY <3>1
    <2> QED  BY <2>3, <2>4, <2>7, <2>8

  \* ---- the environment: a live distribution writer ----
  <1>2. ASSUME NEW i \in Items, Zero(i) PROVE Inv'
    <2> USE <1>2 DEF Zero
    <2>a. selected' = selected                            OBVIOUS
    <2>b. distribution' = [distribution EXCEPT ![i] = 0]  OBVIOUS
    <2>c. i \notin selected                               OBVIOUS
    <2>d. 0 \in 0..MaxProb                                BY MaxProbType
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>d
    <2>2. BoundedSample'
      BY <2>a
    <2>3. SupportConsistency'
      <3> SUFFICES ASSUME NEW s \in selected' PROVE distribution'[s] > 0
        BY DEF SupportConsistency
      <3>1. s \in selected                          BY <2>a
      <3>2. s /= i                                  BY <3>1, <2>c
      <3>3. s \in Items                             BY <3>1
      <3>4. distribution'[s] = distribution[s]      BY <2>b, <3>2, <3>3
      <3> QED  BY <3>1, <3>4
    <2> QED  BY <2>1, <2>2, <2>3

  <1>3. CASE Next
    BY <1>1, <1>2, <1>3 DEF Next
  <1> QED  BY <1>0, <1>3

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                 BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv
THEOREM BoundedSampleSafety == Spec => []BoundedSample  BY Safety, PTL DEF Inv
THEOREM SupportConsistencySafety == Spec => []SupportConsistency
  BY Safety, PTL DEF Inv
====
