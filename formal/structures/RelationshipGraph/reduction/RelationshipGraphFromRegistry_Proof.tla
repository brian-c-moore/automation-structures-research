---- MODULE RelationshipGraphFromRegistry_Proof ----
(***************************************************************************
  TLAPS proof of the ResourceRegistry-to-RelationshipGraph refinement.

  Discharges, unbounded and parametric:

      Refinement == Spec => RG!Spec

  Every behaviour of the ResourceRegistry plus projection views is a
  RelationshipGraph behaviour.

  There is no module-level ASSUME. Nodes is not required to be finite, and the
  proof uses the declared constants only through their set expressions.

  The construction
  reads a pair's weight set back out of the store through a CHOOSE; that
  read is only deterministic because the key maps to at most one value.
  UniqueMapping is carried in the inductive invariant in its directly usable
  functional form (Functional), from which the .cfg's Cardinality-shaped
  RegistryUnique is recovered as a corollary.

  Two projection properties are proved in addition to the refinement:

    AdjacencyConsistencyDefinitional -- the target's AdjacencyConsistency
      holds for the two derived views without a reachability premise.

    NoSelfLoopsSafety -- the target's NoSelfLoops follows from the invariant
      that no registered key is a self-pair.
 ***************************************************************************)
EXTENDS RelationshipGraphFromRegistry, FiniteSetTheorems, TLAPS

(*-------------------------------------------------------------------------*)
(* State-parameterized forms of the construction's projections. The base    *)
(* module's operators read the state variable directly, which makes their   *)
(* primed instances awkward to reason about; these take the store as an     *)
(* argument so one set of lemmas serves both entries and entries'.          *)
(*-------------------------------------------------------------------------*)
WeightsOf(E, s, d) ==
    IF \E S \in WeightSets : << <<s, d>>, S >> \in E
    THEN CHOOSE S \in WeightSets : << <<s, d>>, S >> \in E
    ELSE {}

EdgesOf(E) ==
    {e \in Nodes \X Nodes \X (0..MaxWeight) : e[3] \in WeightsOf(E, e[1], e[2])}

AdjOf(E) == [n \in Nodes |-> {d \in Nodes : WeightsOf(E, n, d) /= {}}]

\* ResourceRegistry's UniqueMapping in the form the read-back needs.
Functional(E) ==
    \A k \in KeyPairs : \A S1, S2 \in WeightSets :
        (<<k, S1>> \in E /\ <<k, S2>> \in E) => S1 = S2

TypeOK ==
    /\ entries \subseteq (KeyPairs \X WeightSets)
    /\ \A e \in entries : e[2] /= {}
    /\ \A e \in entries : e[1][1] /= e[1][2]

Inv == TypeOK /\ Functional(entries)

(*-------------------------------------------------------------------------*)
(* Bridges between the base module's operators and the parameterized ones.  *)
(*-------------------------------------------------------------------------*)
LEMMA TypeBridge == TypeInvariant <=> TypeOK
  BY DEF TypeInvariant, TypeOK, Registry!TypeInvariant

LEMMA WeightsBridge == \A s, d : Weights(s, d) = WeightsOf(entries, s, d)
  BY DEF Weights, WeightsOf

LEMMA ViewBridge == EdgesView = EdgesOf(entries) /\ AdjacencyView = AdjOf(entries)
  BY DEF EdgesView, AdjacencyView, EdgesOf, AdjOf, Weights, WeightsOf

LEMMA ViewBridgePrime ==
        EdgesView' = EdgesOf(entries') /\ AdjacencyView' = AdjOf(entries')
  BY DEF EdgesView, AdjacencyView, EdgesOf, AdjOf, Weights, WeightsOf

(*-------------------------------------------------------------------------*)
(* The read-back lemmas. These are the whole content of "the registry is    *)
(* the graph": a weight set written under a pair is the weight set read     *)
(* back, and an absent pair reads as empty.                                 *)
(*-------------------------------------------------------------------------*)
LEMMA WeightsTyped ==
  ASSUME NEW E, NEW s, NEW d
  PROVE WeightsOf(E, s, d) \in WeightSets
  <1>A. CASE \E S \in WeightSets : << <<s, d>>, S >> \in E
    <2>1. WeightsOf(E, s, d) = CHOOSE S \in WeightSets : << <<s, d>>, S >> \in E
      BY <1>A DEF WeightsOf
    <2>2. (CHOOSE S \in WeightSets : << <<s, d>>, S >> \in E) \in WeightSets
      BY <1>A
    <2> QED BY <2>1, <2>2
  <1>B. CASE ~(\E S \in WeightSets : << <<s, d>>, S >> \in E)
    <2>1. WeightsOf(E, s, d) = {}   BY <1>B DEF WeightsOf
    <2>2. {} \in WeightSets          BY DEF WeightSets
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>A, <1>B

LEMMA WeightsSubset ==
  ASSUME NEW E, NEW s, NEW d
  PROVE WeightsOf(E, s, d) \subseteq 0..MaxWeight
  BY WeightsTyped DEF WeightSets

LEMMA WeightsAbsent ==
  ASSUME NEW E, NEW s, NEW d,
         ~(\E S \in WeightSets : << <<s, d>>, S >> \in E)
  PROVE WeightsOf(E, s, d) = {}
  BY DEF WeightsOf

LEMMA WeightsRead ==
  ASSUME NEW E, Functional(E), NEW s \in Nodes, NEW d \in Nodes,
         NEW S \in WeightSets, << <<s, d>>, S >> \in E
  PROVE WeightsOf(E, s, d) = S
  <1>1. \E T \in WeightSets : << <<s, d>>, T >> \in E
    OBVIOUS
  <1>2. WeightsOf(E, s, d) = CHOOSE T \in WeightSets : << <<s, d>>, T >> \in E
    BY <1>1 DEF WeightsOf
  <1>3. /\ (CHOOSE T \in WeightSets : << <<s, d>>, T >> \in E) \in WeightSets
        /\ << <<s, d>>, (CHOOSE T \in WeightSets : << <<s, d>>, T >> \in E) >> \in E
    BY <1>1
  <1>4. <<s, d>> \in KeyPairs
    BY DEF KeyPairs
  <1> QED BY <1>2, <1>3, <1>4 DEF Functional

LEMMA WeightsAgree ==
  ASSUME NEW E1, NEW E2, Functional(E1), Functional(E2),
         NEW s \in Nodes, NEW d \in Nodes,
         \A S \in WeightSets : (<< <<s, d>>, S >> \in E1)
                                 <=> (<< <<s, d>>, S >> \in E2)
  PROVE WeightsOf(E1, s, d) = WeightsOf(E2, s, d)
  <1>A. CASE \E S \in WeightSets : << <<s, d>>, S >> \in E1
    <2>1. PICK S \in WeightSets : << <<s, d>>, S >> \in E1   BY <1>A
    <2>2. << <<s, d>>, S >> \in E2                            BY <2>1
    <2>3. WeightsOf(E1, s, d) = S    BY <2>1, WeightsRead
    <2>4. WeightsOf(E2, s, d) = S    BY <2>2, WeightsRead
    <2> QED BY <2>3, <2>4
  <1>B. CASE ~(\E S \in WeightSets : << <<s, d>>, S >> \in E1)
    <2>1. ~(\E S \in WeightSets : << <<s, d>>, S >> \in E2)   BY <1>B
    <2>2. WeightsOf(E1, s, d) = {}   BY <1>B, WeightsAbsent
    <2>3. WeightsOf(E2, s, d) = {}   BY <2>1, WeightsAbsent
    <2> QED BY <2>2, <2>3
  <1> QED BY <1>A, <1>B

(*-------------------------------------------------------------------------*)
(* Membership in the flattened edge view, in the form the action proofs     *)
(* keep needing.                                                            *)
(*-------------------------------------------------------------------------*)
LEMMA EdgeMember ==
  ASSUME NEW E, NEW x \in Nodes, NEW y \in Nodes, NEW z \in 0..MaxWeight
  PROVE (<<x, y, z>> \in EdgesOf(E)) <=> (z \in WeightsOf(E, x, y))
  <1>1. <<x, y, z>> \in Nodes \X Nodes \X (0..MaxWeight)
    OBVIOUS
  <1>2. /\ (<<x, y, z>>)[1] = x
        /\ (<<x, y, z>>)[2] = y
        /\ (<<x, y, z>>)[3] = z
    OBVIOUS
  <1> QED BY <1>1, <1>2 DEF EdgesOf

LEMMA EdgeShape ==
  ASSUME NEW E, NEW e \in EdgesOf(E)
  PROVE \E x \in Nodes, y \in Nodes, z \in 0..MaxWeight : e = <<x, y, z>>
  BY DEF EdgesOf

(*-------------------------------------------------------------------------*)
(* AdjacencyConsistency holds directly for the two projection definitions.  *)
(*-------------------------------------------------------------------------*)
LEMMA AdjacencyRedundant ==
  ASSUME NEW E
  PROVE \A src \in Nodes :
          AdjOf(E)[src]
            = {dst \in Nodes : \E w \in 0..MaxWeight : <<src, dst, w>> \in EdgesOf(E)}
  <1> SUFFICES ASSUME NEW src \in Nodes
               PROVE AdjOf(E)[src]
                       = {dst \in Nodes :
                            \E w \in 0..MaxWeight : <<src, dst, w>> \in EdgesOf(E)}
    OBVIOUS
  <1>1. AdjOf(E)[src] = {dst \in Nodes : WeightsOf(E, src, dst) /= {}}
    BY DEF AdjOf
  <1>2. \A dst \in Nodes :
          (\E w \in 0..MaxWeight : <<src, dst, w>> \in EdgesOf(E))
            <=> (WeightsOf(E, src, dst) /= {})
    <2> SUFFICES ASSUME NEW dst \in Nodes
                 PROVE (\E w \in 0..MaxWeight : <<src, dst, w>> \in EdgesOf(E))
                         <=> (WeightsOf(E, src, dst) /= {})
      OBVIOUS
    <2>1. ASSUME NEW w \in 0..MaxWeight, <<src, dst, w>> \in EdgesOf(E)
          PROVE WeightsOf(E, src, dst) /= {}
      BY <2>1, EdgeMember
    <2>2. ASSUME WeightsOf(E, src, dst) /= {}
          PROVE \E w \in 0..MaxWeight : <<src, dst, w>> \in EdgesOf(E)
      <3>1. PICK w \in WeightsOf(E, src, dst) : TRUE   BY <2>2
      <3>2. w \in 0..MaxWeight                          BY <3>1, WeightsSubset
      <3> QED BY <3>1, <3>2, EdgeMember
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2

THEOREM AdjacencyConsistencyDefinitional == RG!AdjacencyConsistency
  BY AdjacencyRedundant, ViewBridge DEF RG!AdjacencyConsistency

(*-------------------------------------------------------------------------*)
(* Init and the inductive step.                                            *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. entries = {}   BY DEF Init
  <1> QED BY <1>1 DEF Inv, TypeOK, Functional

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>c. /\ entries \subseteq (KeyPairs \X WeightSets)
        /\ \A e \in entries : e[2] /= {}
        /\ \A e \in entries : e[1][1] /= e[1][2]
        /\ Functional(entries)
    BY DEF Inv, TypeOK
  <1>0. CASE UNCHANGED vars
    <2>1. entries' = entries   BY <1>0 DEF vars
    <2> QED BY <2>1, <1>c DEF Inv, TypeOK, Functional
  <1>A. CASE \E s, d \in Nodes, w \in 0..MaxWeight : AddEdge(s, d, w)
    <2> SUFFICES ASSUME NEW s \in Nodes, NEW d \in Nodes, NEW w \in 0..MaxWeight,
                        AddEdge(s, d, w)
                 PROVE Inv'
      BY <1>A
    <2>a. s /= d   BY DEF AddEdge
    <2>W. Weights(s, d) \cup {w} \in WeightSets
      <3>1. Weights(s, d) \subseteq 0..MaxWeight
        BY WeightsBridge, WeightsSubset
      <3> QED BY <3>1 DEF WeightSets
    <2>b. entries' = {e \in entries : e[1] /= <<s, d>>}
                       \cup {<< <<s, d>>, Weights(s, d) \cup {w} >>}
      BY DEF AddEdge, Registry!Register
    <2>k. <<s, d>> \in KeyPairs   BY DEF KeyPairs
    <2>1. entries' \subseteq (KeyPairs \X WeightSets)
      BY <2>b, <2>W, <2>k, <1>c
    <2>2. \A e \in entries' : e[2] /= {}
      <3> SUFFICES ASSUME NEW e \in entries' PROVE e[2] /= {}
        OBVIOUS
      <3>A. CASE e \in {f \in entries : f[1] /= <<s, d>>}
        BY <3>A, <1>c
      <3>B. CASE e = << <<s, d>>, Weights(s, d) \cup {w} >>
        <4>1. e[2] = Weights(s, d) \cup {w}   BY <3>B
        <4>2. w \in e[2]                       BY <4>1
        <4> QED BY <4>2
      <3> QED BY <2>b, <3>A, <3>B
    <2>3. \A e \in entries' : e[1][1] /= e[1][2]
      <3> SUFFICES ASSUME NEW e \in entries' PROVE e[1][1] /= e[1][2]
        OBVIOUS
      <3>A. CASE e \in {f \in entries : f[1] /= <<s, d>>}
        BY <3>A, <1>c
      <3>B. CASE e = << <<s, d>>, Weights(s, d) \cup {w} >>
        <4>1. e[1] = <<s, d>>                      BY <3>B
        <4>2. (<<s, d>>)[1] = s /\ (<<s, d>>)[2] = d   OBVIOUS
        <4> QED BY <4>1, <4>2, <2>a
      <3> QED BY <2>b, <3>A, <3>B
    <2>4. Functional(entries')
      <3> SUFFICES ASSUME NEW k \in KeyPairs, NEW S1 \in WeightSets,
                          NEW S2 \in WeightSets,
                          <<k, S1>> \in entries', <<k, S2>> \in entries'
                   PROVE S1 = S2
        BY DEF Functional
      <3>p. (<<k, S1>>)[1] = k /\ (<<k, S2>>)[1] = k   OBVIOUS
      <3>A. CASE k = <<s, d>>
        <4>1. <<k, S1>> \notin {f \in entries : f[1] /= <<s, d>>}
          BY <3>p, <3>A
        <4>2. <<k, S2>> \notin {f \in entries : f[1] /= <<s, d>>}
          BY <3>p, <3>A
        <4>3. <<k, S1>> = << <<s, d>>, Weights(s, d) \cup {w} >>
          BY <2>b, <4>1
        <4>4. <<k, S2>> = << <<s, d>>, Weights(s, d) \cup {w} >>
          BY <2>b, <4>2
        <4> QED BY <4>3, <4>4
      <3>B. CASE k /= <<s, d>>
        <4>1. <<k, S1>> /= << <<s, d>>, Weights(s, d) \cup {w} >>
          BY <3>B
        <4>2. <<k, S2>> /= << <<s, d>>, Weights(s, d) \cup {w} >>
          BY <3>B
        <4>3. <<k, S1>> \in entries /\ <<k, S2>> \in entries
          BY <2>b, <4>1, <4>2
        <4> QED BY <4>3, <1>c DEF Functional
      <3> QED BY <3>A, <3>B
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv, TypeOK
  <1>B. CASE \E s, d \in Nodes : RemoveEdge(s, d)
    <2> SUFFICES ASSUME NEW s \in Nodes, NEW d \in Nodes, RemoveEdge(s, d)
                 PROVE Inv'
      BY <1>B
    <2>b. entries' = {e \in entries : e[1] /= <<s, d>>}
      BY DEF RemoveEdge, Registry!Deregister
    <2>1. entries' \subseteq entries   BY <2>b
    <2> QED BY <2>1, <1>c DEF Inv, TypeOK, Functional
  <1> QED BY <1>0, <1>A, <1>B DEF Next

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* The construction's two .cfg-checked invariants, now unbounded.          *)
(*-------------------------------------------------------------------------*)
THEOREM TypeSafety == Spec => []TypeInvariant
  <1>1. Inv => TypeInvariant   BY TypeBridge DEF Inv
  <1> QED BY Safety, <1>1, PTL

\* The registry instance and this module contain distinct instantiated copies
\* of Cardinality. Expand both definitions once at this boundary.
LEMMA CardBridge == \A S : Registry!Cardinality(S) = Cardinality(S)
  BY DEF Registry!Cardinality, Cardinality

THEOREM RegistryUniqueSafety == Spec => []RegistryUnique
  <1>1. Inv => RegistryUnique
    <2> SUFFICES ASSUME Inv, NEW k \in KeyPairs
                 PROVE Registry!Cardinality(
                           {v \in WeightSets : <<k, v>> \in entries}) <= 1
      BY DEF RegistryUnique, Registry!UniqueMapping
    \* Prove the bound with the local Cardinality, then cross the instance
    \* boundary once through CardBridge.
    <2>1. Cardinality({v \in WeightSets : <<k, v>> \in entries}) <= 1
      <3>A. CASE \E v \in WeightSets : <<k, v>> \in entries
        <4>1. PICK v0 \in WeightSets : <<k, v0>> \in entries   BY <3>A
        <4>2. {v \in WeightSets : <<k, v>> \in entries} = {v0}
          BY <4>1 DEF Inv, Functional
        <4>3. Cardinality({v \in WeightSets : <<k, v>> \in entries}) = 1
          BY <4>2, FS_Singleton
        <4>4. 1 <= 1   OBVIOUS
        <4> QED BY <4>3, <4>4
      <3>B. CASE ~(\E v \in WeightSets : <<k, v>> \in entries)
        <4>1. {v \in WeightSets : <<k, v>> \in entries} = {}   BY <3>B
        <4>2. Cardinality({v \in WeightSets : <<k, v>> \in entries}) = 0
          BY <4>1, FS_EmptySet
        <4>3. 0 <= 1   OBVIOUS
        <4> QED BY <4>2, <4>3
      <3> QED BY <3>A, <3>B
    <2> QED BY <2>1, CardBridge
  <1> QED BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* NoSelfLoops follows from the invariant excluding self-pair keys.          *)
(*-------------------------------------------------------------------------*)
LEMMA NoSelfLoopsFromType == Inv => RG!NoSelfLoops
  <1> SUFFICES ASSUME Inv, NEW n \in Nodes PROVE n \notin AdjacencyView[n]
    BY DEF RG!NoSelfLoops
  <1>1. AdjacencyView[n] = {d \in Nodes : WeightsOf(entries, n, d) /= {}}
    BY ViewBridge DEF AdjOf
  <1>2. ~(\E S \in WeightSets : << <<n, n>>, S >> \in entries)
    <2> SUFFICES ASSUME NEW S \in WeightSets, << <<n, n>>, S >> \in entries
                 PROVE FALSE
      OBVIOUS
    <2>1. (<< <<n, n>>, S >>)[1] = <<n, n>>            OBVIOUS
    <2>2. (<<n, n>>)[1] = n /\ (<<n, n>>)[2] = n       OBVIOUS
    <2> QED BY <2>1, <2>2 DEF Inv, TypeOK
  <1>3. WeightsOf(entries, n, n) = {}   BY <1>2, WeightsAbsent
  <1> QED BY <1>1, <1>3

THEOREM NoSelfLoopsSafety == Spec => []RG!NoSelfLoops
  BY Safety, NoSelfLoopsFromType, PTL

(*-------------------------------------------------------------------------*)
(* The refinement: Init maps to RG!Init, every step maps to a               *)
(* RelationshipGraph step or a stutter.                                    *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => RG!Init
  <1> SUFFICES ASSUME Init PROVE RG!Init
    OBVIOUS
  <1>e. entries = {}   BY DEF Init
  <1>w. \A s, d : WeightsOf(entries, s, d) = {}
    BY <1>e, WeightsAbsent
  <1>1. EdgesView = {}
    <2>1. EdgesOf(entries) = {}
      BY <1>w DEF EdgesOf
    <2> QED BY <2>1, ViewBridge
  <1>2. AdjacencyView = [n \in Nodes |-> {}]
    <2>1. AdjOf(entries) = [n \in Nodes |-> {}]
      BY <1>w DEF AdjOf
    <2> QED BY <2>1, ViewBridge
  <1> QED BY <1>1, <1>2 DEF RG!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [RG!Next]_(RG!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [RG!Next]_(RG!vars)
    OBVIOUS
  <1>i. Inv'   BY NextInv
  <1>f. Functional(entries)    BY DEF Inv
  <1>g. Functional(entries')   BY <1>i DEF Inv
  <1>0. CASE UNCHANGED vars
    <2>1. entries' = entries   BY <1>0 DEF vars
    <2>2. EdgesView' = EdgesView
      BY <2>1, ViewBridge, ViewBridgePrime
    <2>3. AdjacencyView' = AdjacencyView
      BY <2>1, ViewBridge, ViewBridgePrime
    <2> QED BY <2>2, <2>3 DEF RG!vars
  (*----------------------------- AddEdge --------------------------------*)
  <1>A. CASE \E s, d \in Nodes, w \in 0..MaxWeight : AddEdge(s, d, w)
    <2> SUFFICES ASSUME NEW s \in Nodes, NEW d \in Nodes, NEW w \in 0..MaxWeight,
                        AddEdge(s, d, w)
                 PROVE [RG!Next]_(RG!vars)
      BY <1>A
    <2>a. s /= d   BY DEF AddEdge
    <2>W. Weights(s, d) \cup {w} \in WeightSets
      <3>1. Weights(s, d) \subseteq 0..MaxWeight
        BY WeightsBridge, WeightsSubset
      <3> QED BY <3>1 DEF WeightSets
    <2>b. entries' = {e \in entries : e[1] /= <<s, d>>}
                       \cup {<< <<s, d>>, Weights(s, d) \cup {w} >>}
      BY DEF AddEdge, Registry!Register
    \* The pointwise effect on the projection: the touched pair accumulates,
    \* every other pair is untouched.
    <2>K. \A x \in Nodes, y \in Nodes :
            WeightsOf(entries', x, y)
              = IF <<x, y>> = <<s, d>>
                THEN WeightsOf(entries, s, d) \cup {w}
                ELSE WeightsOf(entries, x, y)
      <3> SUFFICES ASSUME NEW x \in Nodes, NEW y \in Nodes
                   PROVE WeightsOf(entries', x, y)
                           = IF <<x, y>> = <<s, d>>
                             THEN WeightsOf(entries, s, d) \cup {w}
                             ELSE WeightsOf(entries, x, y)
        OBVIOUS
      <3>A. CASE <<x, y>> = <<s, d>>
        <4>1. << <<x, y>>, Weights(s, d) \cup {w} >> \in entries'
          BY <2>b, <3>A
        <4>2. WeightsOf(entries', x, y) = Weights(s, d) \cup {w}
          BY <4>1, <2>W, <1>g, WeightsRead
        <4> QED BY <4>2, <3>A, WeightsBridge
      <3>B. CASE <<x, y>> /= <<s, d>>
        <4>1. \A S \in WeightSets : (<< <<x, y>>, S >> \in entries')
                                      <=> (<< <<x, y>>, S >> \in entries)
          <5> SUFFICES ASSUME NEW S \in WeightSets
                       PROVE (<< <<x, y>>, S >> \in entries')
                               <=> (<< <<x, y>>, S >> \in entries)
            OBVIOUS
          <5>1. (<< <<x, y>>, S >>)[1] = <<x, y>>   OBVIOUS
          <5>2. << <<x, y>>, S >> /= << <<s, d>>, Weights(s, d) \cup {w} >>
            BY <3>B
          <5> QED BY <2>b, <5>1, <5>2, <3>B
        <4>2. WeightsOf(entries', x, y) = WeightsOf(entries, x, y)
          BY <4>1, <1>f, <1>g, WeightsAgree
        <4> QED BY <4>2, <3>B
      <3> QED BY <3>A, <3>B
    <2>E. EdgesOf(entries') = EdgesOf(entries) \cup {<<s, d, w>>}
      <3> SUFFICES ASSUME NEW e
                   PROVE (e \in EdgesOf(entries'))
                           <=> (e \in (EdgesOf(entries) \cup {<<s, d, w>>}))
        OBVIOUS
      <3>t. <<s, d, w>> \in Nodes \X Nodes \X (0..MaxWeight)   OBVIOUS
      <3>A. CASE e \in Nodes \X Nodes \X (0..MaxWeight)
        <4>1. PICK x \in Nodes, y \in Nodes, z \in 0..MaxWeight : e = <<x, y, z>>
          BY <3>A
        <4>A. CASE <<x, y>> = <<s, d>>
          <5>1. WeightsOf(entries', x, y) = WeightsOf(entries, s, d) \cup {w}
            BY <2>K, <4>A
          <5>2. (e \in EdgesOf(entries')) <=> (z \in WeightsOf(entries', x, y))
            BY <4>1, EdgeMember
          <5>3. (e \in EdgesOf(entries)) <=> (z \in WeightsOf(entries, x, y))
            BY <4>1, EdgeMember
          <5>4. (e = <<s, d, w>>) <=> (z = w)
            BY <4>1, <4>A
          <5> QED BY <5>1, <5>2, <5>3, <5>4, <4>A
        <4>B. CASE <<x, y>> /= <<s, d>>
          <5>1. WeightsOf(entries', x, y) = WeightsOf(entries, x, y)
            BY <2>K, <4>B
          <5>2. (e \in EdgesOf(entries')) <=> (z \in WeightsOf(entries', x, y))
            BY <4>1, EdgeMember
          <5>3. (e \in EdgesOf(entries)) <=> (z \in WeightsOf(entries, x, y))
            BY <4>1, EdgeMember
          <5>4. e /= <<s, d, w>>
            BY <4>1, <4>B
          <5> QED BY <5>1, <5>2, <5>3, <5>4
        <4> QED BY <4>A, <4>B
      <3>B. CASE e \notin Nodes \X Nodes \X (0..MaxWeight)
        <4>1. e \notin EdgesOf(entries')   BY <3>B DEF EdgesOf
        <4>2. e \notin EdgesOf(entries)    BY <3>B DEF EdgesOf
        <4>3. e /= <<s, d, w>>             BY <3>B, <3>t
        <4> QED BY <4>1, <4>2, <4>3
      <3> QED BY <3>A, <3>B
    <2>J. AdjOf(entries') = [AdjOf(entries) EXCEPT ![s] = @ \cup {d}]
      <3>1. \A n \in Nodes :
              AdjOf(entries')[n] = IF n = s THEN AdjOf(entries)[n] \cup {d}
                                            ELSE AdjOf(entries)[n]
        <4> SUFFICES ASSUME NEW n \in Nodes
                     PROVE AdjOf(entries')[n]
                             = IF n = s THEN AdjOf(entries)[n] \cup {d}
                                        ELSE AdjOf(entries)[n]
          OBVIOUS
        <4>u. AdjOf(entries')[n] = {y \in Nodes : WeightsOf(entries', n, y) /= {}}
          BY DEF AdjOf
        <4>v. AdjOf(entries)[n] = {y \in Nodes : WeightsOf(entries, n, y) /= {}}
          BY DEF AdjOf
        <4>A. CASE n = s
          <5>1. \A y \in Nodes :
                  WeightsOf(entries', n, y)
                    = IF y = d THEN WeightsOf(entries, s, d) \cup {w}
                               ELSE WeightsOf(entries, n, y)
            BY <2>K, <4>A
          <5>2. WeightsOf(entries, s, d) \cup {w} /= {}
            OBVIOUS
          <5>3. {y \in Nodes : WeightsOf(entries', n, y) /= {}}
                  = {y \in Nodes : WeightsOf(entries, n, y) /= {}} \cup {d}
            BY <5>1, <5>2, <4>A
          <5> QED BY <4>u, <4>v, <5>3, <4>A
        <4>B. CASE n /= s
          <5>1. \A y \in Nodes : WeightsOf(entries', n, y) = WeightsOf(entries, n, y)
            BY <2>K, <4>B
          <5> QED BY <4>u, <4>v, <5>1, <4>B
        <4> QED BY <4>A, <4>B
      <3>2. AdjOf(entries) = [n \in Nodes |-> {y \in Nodes : WeightsOf(entries, n, y) /= {}}]
        BY DEF AdjOf
      <3>3. AdjOf(entries') = [n \in Nodes |-> {y \in Nodes : WeightsOf(entries', n, y) /= {}}]
        BY DEF AdjOf
      <3> QED BY <3>1, <3>2, <3>3
    <2>R. RG!AddEdge(s, d, w)
      <3>1. EdgesView' = EdgesView \cup {<<s, d, w>>}
        BY <2>E, ViewBridge, ViewBridgePrime
      <3>2. AdjacencyView' = [AdjacencyView EXCEPT ![s] = @ \cup {d}]
        BY <2>J, ViewBridge, ViewBridgePrime
      <3> QED BY <2>a, <3>1, <3>2 DEF RG!AddEdge
    <2> QED BY <2>R DEF RG!Next
  (*---------------------------- RemoveEdge ------------------------------*)
  <1>B. CASE \E s, d \in Nodes : RemoveEdge(s, d)
    <2> SUFFICES ASSUME NEW s \in Nodes, NEW d \in Nodes, RemoveEdge(s, d)
                 PROVE [RG!Next]_(RG!vars)
      BY <1>B
    <2>a. Weights(s, d) /= {}   BY DEF RemoveEdge
    <2>b. entries' = {e \in entries : e[1] /= <<s, d>>}
      BY DEF RemoveEdge, Registry!Deregister
    <2>K. \A x \in Nodes, y \in Nodes :
            WeightsOf(entries', x, y)
              = IF <<x, y>> = <<s, d>> THEN {} ELSE WeightsOf(entries, x, y)
      <3> SUFFICES ASSUME NEW x \in Nodes, NEW y \in Nodes
                   PROVE WeightsOf(entries', x, y)
                           = IF <<x, y>> = <<s, d>>
                             THEN {} ELSE WeightsOf(entries, x, y)
        OBVIOUS
      <3>A. CASE <<x, y>> = <<s, d>>
        <4>1. ~(\E S \in WeightSets : << <<x, y>>, S >> \in entries')
          <5> SUFFICES ASSUME NEW S \in WeightSets, << <<x, y>>, S >> \in entries'
                       PROVE FALSE
            OBVIOUS
          <5>1. (<< <<x, y>>, S >>)[1] = <<x, y>>   OBVIOUS
          <5> QED BY <2>b, <5>1, <3>A
        <4> QED BY <4>1, WeightsAbsent, <3>A
      <3>B. CASE <<x, y>> /= <<s, d>>
        <4>1. \A S \in WeightSets : (<< <<x, y>>, S >> \in entries')
                                      <=> (<< <<x, y>>, S >> \in entries)
          <5> SUFFICES ASSUME NEW S \in WeightSets
                       PROVE (<< <<x, y>>, S >> \in entries')
                               <=> (<< <<x, y>>, S >> \in entries)
            OBVIOUS
          <5>1. (<< <<x, y>>, S >>)[1] = <<x, y>>   OBVIOUS
          <5> QED BY <2>b, <5>1, <3>B
        <4>2. WeightsOf(entries', x, y) = WeightsOf(entries, x, y)
          BY <4>1, <1>f, <1>g, WeightsAgree
        <4> QED BY <4>2, <3>B
      <3> QED BY <3>A, <3>B
    <2>G. \E ww \in 0..MaxWeight : <<s, d, ww>> \in EdgesOf(entries)
      <3>1. WeightsOf(entries, s, d) /= {}   BY <2>a, WeightsBridge
      <3>2. PICK ww \in WeightsOf(entries, s, d) : TRUE   BY <3>1
      <3>3. ww \in 0..MaxWeight   BY <3>2, WeightsSubset
      <3> QED BY <3>2, <3>3, EdgeMember
    <2>E. EdgesOf(entries') = {e \in EdgesOf(entries) : ~(e[1] = s /\ e[2] = d)}
      <3> SUFFICES ASSUME NEW e
                   PROVE (e \in EdgesOf(entries'))
                           <=> (e \in {f \in EdgesOf(entries) : ~(f[1] = s /\ f[2] = d)})
        OBVIOUS
      <3>A. CASE e \in Nodes \X Nodes \X (0..MaxWeight)
        <4>1. PICK x \in Nodes, y \in Nodes, z \in 0..MaxWeight : e = <<x, y, z>>
          BY <3>A
        <4>p. e[1] = x /\ e[2] = y   BY <4>1
        <4>2. (e \in EdgesOf(entries')) <=> (z \in WeightsOf(entries', x, y))
          BY <4>1, EdgeMember
        <4>3. (e \in EdgesOf(entries)) <=> (z \in WeightsOf(entries, x, y))
          BY <4>1, EdgeMember
        <4>A. CASE <<x, y>> = <<s, d>>
          <5>1. WeightsOf(entries', x, y) = {}   BY <2>K, <4>A
          <5>2. x = s /\ y = d                    BY <4>A
          <5> QED BY <4>2, <5>1, <4>p, <5>2
        <4>B. CASE <<x, y>> /= <<s, d>>
          <5>1. WeightsOf(entries', x, y) = WeightsOf(entries, x, y)
            BY <2>K, <4>B
          <5>2. ~(x = s /\ y = d)   BY <4>B
          <5> QED BY <4>2, <4>3, <5>1, <4>p, <5>2
        <4> QED BY <4>A, <4>B
      <3>B. CASE e \notin Nodes \X Nodes \X (0..MaxWeight)
        <4>1. e \notin EdgesOf(entries')   BY <3>B DEF EdgesOf
        <4>2. e \notin EdgesOf(entries)    BY <3>B DEF EdgesOf
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>A, <3>B
    <2>J. AdjOf(entries') = [AdjOf(entries) EXCEPT ![s] = @ \ {d}]
      <3>1. \A n \in Nodes :
              AdjOf(entries')[n] = IF n = s THEN AdjOf(entries)[n] \ {d}
                                            ELSE AdjOf(entries)[n]
        <4> SUFFICES ASSUME NEW n \in Nodes
                     PROVE AdjOf(entries')[n]
                             = IF n = s THEN AdjOf(entries)[n] \ {d}
                                        ELSE AdjOf(entries)[n]
          OBVIOUS
        <4>u. AdjOf(entries')[n] = {y \in Nodes : WeightsOf(entries', n, y) /= {}}
          BY DEF AdjOf
        <4>v. AdjOf(entries)[n] = {y \in Nodes : WeightsOf(entries, n, y) /= {}}
          BY DEF AdjOf
        <4>A. CASE n = s
          <5>1. \A y \in Nodes :
                  WeightsOf(entries', n, y)
                    = IF y = d THEN {} ELSE WeightsOf(entries, n, y)
            BY <2>K, <4>A
          <5>2. {y \in Nodes : WeightsOf(entries', n, y) /= {}}
                  = {y \in Nodes : WeightsOf(entries, n, y) /= {}} \ {d}
            BY <5>1, <4>A
          <5> QED BY <4>u, <4>v, <5>2, <4>A
        <4>B. CASE n /= s
          <5>1. \A y \in Nodes : WeightsOf(entries', n, y) = WeightsOf(entries, n, y)
            BY <2>K, <4>B
          <5> QED BY <4>u, <4>v, <5>1, <4>B
        <4> QED BY <4>A, <4>B
      <3>2. AdjOf(entries) = [n \in Nodes |-> {y \in Nodes : WeightsOf(entries, n, y) /= {}}]
        BY DEF AdjOf
      <3>3. AdjOf(entries') = [n \in Nodes |-> {y \in Nodes : WeightsOf(entries', n, y) /= {}}]
        BY DEF AdjOf
      <3> QED BY <3>1, <3>2, <3>3
    <2>R. RG!RemoveEdge(s, d)
      <3>1. \E ww \in 0..MaxWeight : <<s, d, ww>> \in EdgesView
        BY <2>G, ViewBridge
      <3>2. EdgesView' = {e \in EdgesView : ~(e[1] = s /\ e[2] = d)}
        BY <2>E, ViewBridge, ViewBridgePrime
      <3>3. AdjacencyView' = [AdjacencyView EXCEPT ![s] = @ \ {d}]
        BY <2>J, ViewBridge, ViewBridgePrime
      <3> QED BY <3>1, <3>2, <3>3 DEF RG!RemoveEdge
    <2> QED BY <2>R DEF RG!Next
  <1> QED BY <1>0, <1>A, <1>B DEF Next

(*-------------------------------------------------------------------------*)
(* The main result: the construction refines RelationshipGraph, unbounded.  *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => RG!Spec
  <1>1. Init => RG!Init                                 BY InitRefines
  <1>2. Inv /\ [Next]_vars => [RG!Next]_(RG!vars)       BY NextRefines
  <1>3. Spec => []Inv                                   BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, RG!Spec

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => RelationshipGraphRefinement
  BY Refinement DEF RelationshipGraphRefinement

====
