---- MODULE ActuationPassFromRegistry_Proof ----
(***************************************************************************
  TLAPS proof of the ActuationPass minimality re-run.

  Discharges, unbounded and parametric:

      Refinement == Spec => APL!Spec

  NO MODULE-LEVEL ASSUME. Parametric in Seats, Resources and NULL; in
  particular it does NOT need NULL \notin Resources, matching the carriers'
  parametricity (STRUCTURE_ASSUMPTIONS records no contract for either
  ActuationPass or ResourceRegistry).

  The refinement is proved unbounded even though the entry does not reduce
  from the catalog, because O3 (PassCompleteness) lands on the declared
  Marker glue and no component absorbs it. Proving it at the parametric tier
  rather than the bounded one makes the verdict rest on which stratum carries
  the obligation rather than on the strength of the construction.

  ALSO PROVED:

      ScopeEmergent    == Spec => []APL!ActuationScope
      FidelityEmergent == Spec => []APL!EffectFidelity

  Both are carried by an inductive invariant over the construction's state.
  O1 and O2 do NOT route onto ResourceRegistry. What maintains them here is
  this construction's own CDeallocate ownership guard; what ResourceRegistry
  supplies is the deterministic keyed read that makes the defaulted views
  well defined. That is why these theorems are carried as
  ScopeEmergent/FidelityEmergent OVER THE CONSTRUCTION rather than as
  component-supplied facts. O3 is NOT claimed emergent here: it holds of the
  construction, but it holds because of the Marker's fused check and the
  closure freeze.
 ***************************************************************************)
EXTENDS ActuationPassFromRegistry, FiniteSetTheorems, TLAPS

\* ResourceRegistry's UniqueMapping in the form the read-back needs, once
\* per instance.
FunctionalIn(E) ==
    \A k \in Seats : \A v1, v2 \in Resources :
        (<<k, v1>> \in E /\ <<k, v2>> \in E) => v1 = v2

TypeOK ==
    /\ e_alloc \subseteq (Seats \X Resources)
    /\ e_eff   \subseteq (Seats \X Resources)
    /\ complete \in BOOLEAN

\* The two halves that reduce: an applied seat is a registered seat, and the
\* effect it recorded is that seat's registered resource.
FidelityOK ==
    \A s \in Seats : ReadE(s) /= NULL => ReadE(s) = ReadA(s)

Inv == TypeOK /\ FunctionalIn(e_alloc) /\ FunctionalIn(e_eff) /\ FidelityOK

LEMMA TypeBridge == TypeInvariant <=> TypeOK
  BY DEF TypeInvariant, TypeOK, RegA!TypeInvariant, RegE!TypeInvariant

(*-------------------------------------------------------------------------*)
(* Read-back lemmas for the defaulted view, stated once over the            *)
(* parameterized reader and reused by both instances.                       *)
(*-------------------------------------------------------------------------*)
LEMMA ReadTyped ==
  ASSUME NEW E, NEW s
  PROVE ReadIn(E, s) \in Resources \cup {NULL}
  <1>A. CASE \E r \in Resources : <<s, r>> \in E
    <2>1. ReadIn(E, s) = CHOOSE r \in Resources : <<s, r>> \in E
      BY <1>A DEF ReadIn
    <2>2. (CHOOSE r \in Resources : <<s, r>> \in E) \in Resources
      BY <1>A
    <2> QED BY <2>1, <2>2
  <1>B. CASE ~(\E r \in Resources : <<s, r>> \in E)
    <2>1. ReadIn(E, s) = NULL   BY <1>B DEF ReadIn
    <2> QED BY <2>1
  <1> QED BY <1>A, <1>B

LEMMA ReadAbsent ==
  ASSUME NEW E, NEW s, ~(\E r \in Resources : <<s, r>> \in E)
  PROVE ReadIn(E, s) = NULL
  BY DEF ReadIn

\* Under UniqueMapping, a registered key reads back as its registered value.
LEMMA ReadPresent ==
  ASSUME NEW E, NEW s, NEW v \in Resources, <<s, v>> \in E,
         \A v1, v2 \in Resources :
             (<<s, v1>> \in E /\ <<s, v2>> \in E) => v1 = v2
  PROVE ReadIn(E, s) = v
  <1>1. \E r \in Resources : <<s, r>> \in E   OBVIOUS
  <1>2. ReadIn(E, s) = CHOOSE r \in Resources : <<s, r>> \in E
    BY <1>1 DEF ReadIn
  <1>3. (CHOOSE r \in Resources : <<s, r>> \in E) \in Resources
    BY <1>1
  <1>4. <<s, (CHOOSE r \in Resources : <<s, r>> \in E)>> \in E
    BY <1>1
  <1> QED BY <1>2, <1>3, <1>4

(*-------------------------------------------------------------------------*)
(* Register / Deregister read-back, over an arbitrary entry set.            *)
(*-------------------------------------------------------------------------*)
LEMMA RegisterReadBack ==
  ASSUME NEW E, E \subseteq (Seats \X Resources),
         NEW k \in Seats, NEW v \in Resources,
         NEW t,
         FunctionalIn(E)
  PROVE  LET E2 == {x \in E : x[1] /= k} \cup {<<k, v>>}
         IN  /\ FunctionalIn(E2)
             /\ E2 \subseteq (Seats \X Resources)
             /\ ReadIn(E2, t) = IF t = k THEN v ELSE ReadIn(E, t)
  <1> DEFINE E2 == {x \in E : x[1] /= k} \cup {<<k, v>>}
  <1>T. E2 \subseteq (Seats \X Resources)
    OBVIOUS
  <1>F. FunctionalIn(E2)
    <2> SUFFICES ASSUME NEW j \in Seats, NEW v1 \in Resources, NEW v2 \in Resources,
                        <<j, v1>> \in E2, <<j, v2>> \in E2
                 PROVE  v1 = v2
      BY DEF FunctionalIn
    <2>1. CASE j = k
      \* only <<k, v>> survives for key k
      <3>1. <<j, v1>> \notin {x \in E : x[1] /= k}   BY <2>1
      <3>2. <<j, v2>> \notin {x \in E : x[1] /= k}   BY <2>1
      <3> QED BY <3>1, <3>2
    <2>2. CASE j /= k
      <3>1. <<j, v1>> \in E   BY <2>2
      <3>2. <<j, v2>> \in E   BY <2>2
      <3> QED BY <3>1, <3>2, FunctionalIn(E) DEF FunctionalIn
    <2> QED BY <2>1, <2>2
  <1>R. ReadIn(E2, t) = IF t = k THEN v ELSE ReadIn(E, t)
    <2>1. CASE t = k
      <3>1. <<t, v>> \in E2   BY <2>1
      <3>2. \A v1, v2 \in Resources :
                (<<t, v1>> \in E2 /\ <<t, v2>> \in E2) => v1 = v2
        BY <1>F, <2>1 DEF FunctionalIn
      <3>3. ReadIn(E2, t) = v   BY <3>1, <3>2, ReadPresent, <1>T
      <3> QED BY <3>3, <2>1
    <2>2. CASE t /= k
      <3>1. \A r : (<<t, r>> \in E2) <=> (<<t, r>> \in E)   BY <2>2
      <3>2. (\E r \in Resources : <<t, r>> \in E2)
              <=> (\E r \in Resources : <<t, r>> \in E)     BY <3>1
      <3>3. (CHOOSE r \in Resources : <<t, r>> \in E2)
              = (CHOOSE r \in Resources : <<t, r>> \in E)   BY <3>1
      <3>4. ReadIn(E2, t) = ReadIn(E, t)   BY <3>2, <3>3 DEF ReadIn
      <3> QED BY <3>4, <2>2
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>T, <1>F, <1>R

LEMMA DeregisterReadBack ==
  ASSUME NEW E, E \subseteq (Seats \X Resources),
         NEW k, NEW t,
         FunctionalIn(E)
  PROVE  LET E2 == {x \in E : x[1] /= k}
         IN  /\ FunctionalIn(E2)
             /\ E2 \subseteq (Seats \X Resources)
             /\ ReadIn(E2, t) = IF t = k THEN NULL ELSE ReadIn(E, t)
  <1> DEFINE E2 == {x \in E : x[1] /= k}
  <1>T. E2 \subseteq (Seats \X Resources)
    OBVIOUS
  <1>F. FunctionalIn(E2)
    BY FunctionalIn(E) DEF FunctionalIn
  <1>R. ReadIn(E2, t) = IF t = k THEN NULL ELSE ReadIn(E, t)
    <2>1. CASE t = k
      <3>1. ~(\E r \in Resources : <<t, r>> \in E2)   BY <2>1
      <3>2. ReadIn(E2, t) = NULL   BY <3>1, ReadAbsent
      <3> QED BY <3>2, <2>1
    <2>2. CASE t /= k
      <3>1. \A r : (<<t, r>> \in E2) <=> (<<t, r>> \in E)   BY <2>2
      <3>2. (\E r \in Resources : <<t, r>> \in E2)
              <=> (\E r \in Resources : <<t, r>> \in E)     BY <3>1
      <3>3. (CHOOSE r \in Resources : <<t, r>> \in E2)
              = (CHOOSE r \in Resources : <<t, r>> \in E)   BY <3>1
      <3>4. ReadIn(E2, t) = ReadIn(E, t)   BY <3>2, <3>3 DEF ReadIn
      <3> QED BY <3>4, <2>2
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>T, <1>F, <1>R

(*-------------------------------------------------------------------------*)
(* Safety of the construction's invariants.                                *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. PICK D \in SUBSET Seats, f \in [Seats -> Resources] :
            e_alloc = {<<s, f[s]>> : s \in D}
    BY DEF Init
  <1>2. TypeOK
    BY <1>1 DEF Init, TypeOK
  <1>3. FunctionalIn(e_alloc)
    BY <1>1 DEF FunctionalIn
  <1>4. FunctionalIn(e_eff)
    BY DEF Init, FunctionalIn
  <1>5. FidelityOK
    <2> SUFFICES ASSUME NEW s \in Seats PROVE ReadE(s) = NULL
      BY DEF FidelityOK
    <2>1. e_eff = {}   BY DEF Init
    <2>2. ~(\E r \in Resources : <<s, r>> \in e_eff)   BY <2>1
    <2> QED BY <2>2, ReadAbsent DEF ReadE
  <1> QED BY <1>2, <1>3, <1>4, <1>5 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1>c. /\ e_alloc \subseteq (Seats \X Resources)
        /\ e_eff \subseteq (Seats \X Resources)
        /\ complete \in BOOLEAN
        /\ FunctionalIn(e_alloc)
        /\ FunctionalIn(e_eff)
        /\ FidelityOK
    BY DEF Inv, TypeOK

  <1>0. CASE UNCHANGED vars
    <2>1. e_alloc' = e_alloc /\ e_eff' = e_eff /\ complete' = complete
      BY <1>0 DEF vars
    <2> QED BY <2>1, <1>c DEF Inv, TypeOK, FunctionalIn, FidelityOK,
                              ReadA, ReadE

  <1>A. ASSUME NEW s \in Seats, CActuate(s) PROVE Inv'
    <2> USE <1>A DEF CActuate
    <2>a. /\ e_alloc' = e_alloc
          /\ complete' = complete
          /\ e_eff' = {x \in e_eff : x[1] /= s} \cup {<<s, ReadA(s)>>}
          /\ ReadA(s) /= NULL
      OBVIOUS
    <2>v. ReadA(s) \in Resources
      BY <2>a, ReadTyped DEF ReadA
    <2>b. /\ FunctionalIn(e_eff')
          /\ e_eff' \subseteq (Seats \X Resources)
          /\ \A t : ReadIn(e_eff', t)
                      = IF t = s THEN ReadA(s) ELSE ReadIn(e_eff, t)
      BY <2>a, <2>v, <1>c, RegisterReadBack
    <2>d. \A t : ReadA(t)' = ReadA(t)
      BY <2>a DEF ReadA
    <2>1. TypeOK'
      BY <2>a, <2>b, <1>c DEF TypeOK
    <2>2. FunctionalIn(e_alloc)'
      BY <2>a, <1>c DEF FunctionalIn
    <2>3. FunctionalIn(e_eff)'
      BY <2>b
    <2>4. FidelityOK'
      <3> SUFFICES ASSUME NEW t \in Seats, ReadE(t)' /= NULL
                   PROVE  ReadE(t)' = ReadA(t)'
        BY DEF FidelityOK
      <3>0. ReadE(t)' = ReadIn(e_eff', t)   BY DEF ReadE
      <3>1. CASE t = s
        <4>1. ReadE(t)' = ReadA(s)   BY <3>0, <2>b, <3>1
        <4> QED BY <4>1, <2>d, <3>1
      <3>2. CASE t /= s
        <4>1. ReadE(t)' = ReadIn(e_eff, t)   BY <3>0, <2>b, <3>2
        <4>2. ReadE(t) = ReadIn(e_eff, t)    BY DEF ReadE
        <4>3. ReadE(t) = ReadA(t)            BY <4>1, <4>2, <1>c DEF FidelityOK
        <4> QED BY <4>1, <4>2, <4>3, <2>d
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv

  <1>B. ASSUME NEW s \in Seats, NEW r \in Resources, CAllocate(s, r) PROVE Inv'
    <2> USE <1>B DEF CAllocate
    <2>a. /\ e_eff' = e_eff
          /\ complete' = complete
          /\ e_alloc' = {x \in e_alloc : x[1] /= s} \cup {<<s, r>>}
          /\ ReadA(s) = NULL
      OBVIOUS
    <2>b. /\ FunctionalIn(e_alloc')
          /\ e_alloc' \subseteq (Seats \X Resources)
          /\ \A t : ReadIn(e_alloc', t)
                      = IF t = s THEN r ELSE ReadIn(e_alloc, t)
      BY <2>a, <1>c, RegisterReadBack
    <2>d. \A t : ReadE(t)' = ReadE(t)
      BY <2>a DEF ReadE
    <2>1. TypeOK'
      BY <2>a, <2>b, <1>c DEF TypeOK
    <2>2. FunctionalIn(e_alloc)'
      BY <2>b
    <2>3. FunctionalIn(e_eff)'
      BY <2>a, <1>c DEF FunctionalIn
    <2>4. FidelityOK'
      <3> SUFFICES ASSUME NEW t \in Seats, ReadE(t)' /= NULL
                   PROVE  ReadE(t)' = ReadA(t)'
        BY DEF FidelityOK
      <3>0. /\ ReadE(t)' = ReadE(t)
            /\ ReadA(t)' = ReadIn(e_alloc', t)
        BY <2>d DEF ReadA
      <3>1. ReadE(t) = ReadA(t)   BY <3>0, <1>c DEF FidelityOK
      <3>2. CASE t = s
        \* the seat was unregistered, so by FidelityOK it was unapplied; the
        \* antecedent is contradictory.
        <4>1. ReadE(t) = NULL   BY <3>1, <2>a, <3>2
        <4> QED BY <4>1, <3>0
      <3>3. CASE t /= s
        <4>1. ReadA(t)' = ReadIn(e_alloc, t)   BY <3>0, <2>b, <3>3
        <4>2. ReadA(t) = ReadIn(e_alloc, t)    BY DEF ReadA
        <4> QED BY <4>1, <4>2, <3>0, <3>1
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv

  <1>C. ASSUME NEW s \in Seats, CDeallocate(s) PROVE Inv'
    <2> USE <1>C DEF CDeallocate
    <2>a. /\ e_eff' = e_eff
          /\ complete' = complete
          /\ e_alloc' = {x \in e_alloc : x[1] /= s}
          /\ ReadE(s) = NULL
      OBVIOUS
    <2>b. /\ FunctionalIn(e_alloc')
          /\ e_alloc' \subseteq (Seats \X Resources)
          /\ \A t : ReadIn(e_alloc', t)
                      = IF t = s THEN NULL ELSE ReadIn(e_alloc, t)
      BY <2>a, <1>c, DeregisterReadBack
    <2>d. \A t : ReadE(t)' = ReadE(t)
      BY <2>a DEF ReadE
    <2>1. TypeOK'
      BY <2>a, <2>b, <1>c DEF TypeOK
    <2>2. FunctionalIn(e_alloc)'
      BY <2>b
    <2>3. FunctionalIn(e_eff)'
      BY <2>a, <1>c DEF FunctionalIn
    <2>4. FidelityOK'
      <3> SUFFICES ASSUME NEW t \in Seats, ReadE(t)' /= NULL
                   PROVE  ReadE(t)' = ReadA(t)'
        BY DEF FidelityOK
      <3>0. /\ ReadE(t)' = ReadE(t)
            /\ ReadA(t)' = ReadIn(e_alloc', t)
        BY <2>d DEF ReadA
      <3>1. ReadE(t) = ReadA(t)   BY <3>0, <1>c DEF FidelityOK
      <3>2. CASE t = s
        \* withdrawal is guarded by the ownership clause: an applied seat is
        \* never deregistered, so the antecedent is contradictory.
        <4> QED BY <2>a, <3>0, <3>2
      <3>3. CASE t /= s
        <4>1. ReadA(t)' = ReadIn(e_alloc, t)   BY <3>0, <2>b, <3>3
        <4>2. ReadA(t) = ReadIn(e_alloc, t)    BY DEF ReadA
        <4> QED BY <4>1, <4>2, <3>0, <3>1
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv

  <1>D. ASSUME CFinish PROVE Inv'
    <2> USE <1>D DEF CFinish
    <2>a. /\ e_alloc' = e_alloc
          /\ e_eff' = e_eff
          /\ complete' = TRUE
      OBVIOUS
    <2> QED BY <2>a, <1>c DEF Inv, TypeOK, FunctionalIn, FidelityOK,
                              ReadA, ReadE

  <1>E. CASE Next
    BY <1>A, <1>B, <1>C, <1>D, <1>E DEF Next
  <1> QED BY <1>0, <1>E

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
  <1>1. Inv => TypeInvariant   BY TypeBridge DEF Inv
  <1> QED BY Safety, <1>1, PTL

\* Bridge the instance-qualified Cardinality to the local one ONCE: an
\* instance-qualified operator is not definitionally the local one.
LEMMA CardBridgeA == \A S : RegA!Cardinality(S) = Cardinality(S)
  BY DEF RegA!Cardinality, Cardinality
LEMMA CardBridgeE == \A S : RegE!Cardinality(S) = Cardinality(S)
  BY DEF RegE!Cardinality, Cardinality

LEMMA UniqueFromFunctional ==
  ASSUME NEW E, FunctionalIn(E), NEW k \in Seats
  PROVE  Cardinality({v \in Resources : <<k, v>> \in E}) <= 1
  <1>A. CASE \E v \in Resources : <<k, v>> \in E
    <2>1. PICK v0 \in Resources : <<k, v0>> \in E   BY <1>A
    <2>2. {v \in Resources : <<k, v>> \in E} = {v0}
      BY <2>1 DEF FunctionalIn
    <2>3. Cardinality({v \in Resources : <<k, v>> \in E}) = 1
      BY <2>2, FS_Singleton
    <2> QED BY <2>3
  <1>B. CASE ~(\E v \in Resources : <<k, v>> \in E)
    <2>1. {v \in Resources : <<k, v>> \in E} = {}   BY <1>B
    <2>2. Cardinality({v \in Resources : <<k, v>> \in E}) = 0
      BY <2>1, FS_EmptySet
    <2> QED BY <2>2
  <1> QED BY <1>A, <1>B

THEOREM AllocUniqueSafety == Spec => []AllocUnique
  <1>1. Inv => AllocUnique
    <2> SUFFICES ASSUME Inv, NEW k \in Seats
                 PROVE RegA!Cardinality(
                           {v \in Resources : <<k, v>> \in e_alloc}) <= 1
      BY DEF AllocUnique, RegA!UniqueMapping
    <2> QED BY UniqueFromFunctional, CardBridgeA DEF Inv
  <1> QED BY Safety, <1>1, PTL

THEOREM EffUniqueSafety == Spec => []EffUnique
  <1>1. Inv => EffUnique
    <2> SUFFICES ASSUME Inv, NEW k \in Seats
                 PROVE RegE!Cardinality(
                           {v \in Resources : <<k, v>> \in e_eff}) <= 1
      BY DEF EffUnique, RegE!UniqueMapping
    <2> QED BY UniqueFromFunctional, CardBridgeE DEF Inv
  <1> QED BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* THE HALVES THAT REDUCE: O1 and O2 are carried by the registries.         *)
(*-------------------------------------------------------------------------*)
THEOREM FidelityEmergent == Spec => []APL!EffectFidelity
  <1>1. Inv => APL!EffectFidelity
    <2> SUFFICES ASSUME Inv, NEW s \in Seats, EffView[s] /= NULL
                 PROVE  EffView[s] = AllocView[s]
      BY DEF APL!EffectFidelity
    <2>1. EffView[s] = ReadE(s)      BY DEF EffView
    <2>2. AllocView[s] = ReadA(s)    BY DEF AllocView
    <2> QED BY <2>1, <2>2 DEF Inv, FidelityOK
  <1> QED BY Safety, <1>1, PTL

THEOREM ScopeEmergent == Spec => []APL!ActuationScope
  <1>1. Inv => APL!ActuationScope
    <2> SUFFICES ASSUME Inv, NEW s \in Seats, EffView[s] /= NULL
                 PROVE  AllocView[s] /= NULL
      BY DEF APL!ActuationScope, APL!Actuated
    <2>1. EffView[s] = ReadE(s)      BY DEF EffView
    <2>2. AllocView[s] = ReadA(s)    BY DEF AllocView
    <2>3. ReadE(s) = ReadA(s)        BY <2>1 DEF Inv, FidelityOK
    <2> QED BY <2>1, <2>2, <2>3
  <1> QED BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement.                                                         *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => APL!Init
  <1> SUFFICES ASSUME Init PROVE APL!Init  OBVIOUS
  <1>1. AllocView \in [Seats -> Resources \cup {NULL}]
    BY ReadTyped DEF AllocView, ReadA
  <1>2. EffView = [s \in Seats |-> NULL]
    <2> SUFFICES ASSUME NEW s \in Seats PROVE ReadE(s) = NULL
      BY DEF EffView
    <2>1. e_eff = {}   BY DEF Init
    <2>2. ~(\E r \in Resources : <<s, r>> \in e_eff)   BY <2>1
    <2> QED BY <2>2, ReadAbsent DEF ReadE
  <1>3. complete = FALSE   BY DEF Init
  <1> QED BY <1>1, <1>2, <1>3 DEF APL!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [APL!Next]_(APL!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [APL!Next]_(APL!vars)  OBVIOUS
  <1>c. /\ e_alloc \subseteq (Seats \X Resources)
        /\ e_eff \subseteq (Seats \X Resources)
        /\ complete \in BOOLEAN
        /\ FunctionalIn(e_alloc)
        /\ FunctionalIn(e_eff)
        /\ FidelityOK
    BY DEF Inv, TypeOK

  <1>0. CASE UNCHANGED vars
    <2>1. e_alloc' = e_alloc /\ e_eff' = e_eff /\ complete' = complete
      BY <1>0 DEF vars
    <2>2. AllocView' = AllocView   BY <2>1 DEF AllocView, ReadA
    <2>3. EffView' = EffView       BY <2>1 DEF EffView, ReadE
    <2> QED BY <2>1, <2>2, <2>3 DEF APL!vars

  <1>A. ASSUME NEW s \in Seats, CActuate(s) PROVE [APL!Next]_(APL!vars)
    <2> USE <1>A DEF CActuate
    <2>a. /\ ~complete
          /\ ReadE(s) = NULL
          /\ ReadA(s) /= NULL
          /\ e_alloc' = e_alloc
          /\ complete' = complete
          /\ e_eff' = {x \in e_eff : x[1] /= s} \cup {<<s, ReadA(s)>>}
      OBVIOUS
    <2>v. ReadA(s) \in Resources
      BY <2>a, ReadTyped DEF ReadA
    <2>b. \A t : ReadIn(e_eff', t)
                   = IF t = s THEN ReadA(s) ELSE ReadIn(e_eff, t)
      BY <2>a, <2>v, <1>c, RegisterReadBack
    <2>1. AllocView' = AllocView   BY <2>a DEF AllocView, ReadA
    <2>2. EffView[s] = NULL        BY <2>a DEF EffView
    <2>3. AllocView[s] /= NULL     BY <2>a DEF AllocView
    <2>4. EffView' = [EffView EXCEPT ![s] = AllocView[s]]
      <3>1. EffView' = [t \in Seats |-> ReadIn(e_eff', t)]
        BY DEF EffView, ReadE
      <3>2. EffView' = [t \in Seats |->
                          IF t = s THEN ReadA(s) ELSE ReadIn(e_eff, t)]
        BY <3>1, <2>b
      <3>3. [EffView EXCEPT ![s] = AllocView[s]]
              = [t \in Seats |-> IF t = s THEN ReadA(s) ELSE ReadE(t)]
        BY <2>3 DEF EffView, AllocView
      <3> QED BY <3>2, <3>3 DEF ReadE
    <2>5. APL!Actuate(s)
      BY <2>a, <2>1, <2>2, <2>3, <2>4 DEF APL!Actuate
    <2> QED BY <2>5 DEF APL!Next

  <1>B. ASSUME NEW s \in Seats, NEW r \in Resources, CAllocate(s, r)
        PROVE [APL!Next]_(APL!vars)
    <2> USE <1>B DEF CAllocate
    <2>a. /\ ~complete
          /\ ReadA(s) = NULL
          /\ e_eff' = e_eff
          /\ complete' = complete
          /\ e_alloc' = {x \in e_alloc : x[1] /= s} \cup {<<s, r>>}
      OBVIOUS
    <2>b. \A t : ReadIn(e_alloc', t)
                   = IF t = s THEN r ELSE ReadIn(e_alloc, t)
      BY <2>a, <1>c, RegisterReadBack
    <2>1. EffView' = EffView       BY <2>a DEF EffView, ReadE
    <2>2. AllocView[s] = NULL      BY <2>a DEF AllocView
    <2>3. AllocView' = [AllocView EXCEPT ![s] = r]
      <3>1. AllocView' = [t \in Seats |-> ReadIn(e_alloc', t)]
        BY DEF AllocView, ReadA
      <3>2. AllocView' = [t \in Seats |->
                            IF t = s THEN r ELSE ReadIn(e_alloc, t)]
        BY <3>1, <2>b
      <3>3. [AllocView EXCEPT ![s] = r]
              = [t \in Seats |-> IF t = s THEN r ELSE ReadA(t)]
        BY DEF AllocView
      <3> QED BY <3>2, <3>3 DEF ReadA
    <2>4. APL!Allocate(s, r)
      BY <2>a, <2>1, <2>2, <2>3 DEF APL!Allocate
    <2> QED BY <2>4 DEF APL!Next

  <1>C. ASSUME NEW s \in Seats, CDeallocate(s) PROVE [APL!Next]_(APL!vars)
    <2> USE <1>C DEF CDeallocate
    <2>a. /\ ~complete
          /\ ReadA(s) /= NULL
          /\ ReadE(s) = NULL
          /\ e_eff' = e_eff
          /\ complete' = complete
          /\ e_alloc' = {x \in e_alloc : x[1] /= s}
      OBVIOUS
    <2>b. \A t : ReadIn(e_alloc', t)
                   = IF t = s THEN NULL ELSE ReadIn(e_alloc, t)
      BY <2>a, <1>c, DeregisterReadBack
    <2>1. EffView' = EffView       BY <2>a DEF EffView, ReadE
    <2>2. AllocView[s] /= NULL     BY <2>a DEF AllocView
    <2>3. EffView[s] = NULL        BY <2>a DEF EffView
    <2>4. AllocView' = [AllocView EXCEPT ![s] = NULL]
      <3>1. AllocView' = [t \in Seats |-> ReadIn(e_alloc', t)]
        BY DEF AllocView, ReadA
      <3>2. AllocView' = [t \in Seats |->
                            IF t = s THEN NULL ELSE ReadIn(e_alloc, t)]
        BY <3>1, <2>b
      <3>3. [AllocView EXCEPT ![s] = NULL]
              = [t \in Seats |-> IF t = s THEN NULL ELSE ReadA(t)]
        BY DEF AllocView
      <3> QED BY <3>2, <3>3 DEF ReadA
    <2>5. APL!Deallocate(s)
      BY <2>a, <2>1, <2>2, <2>3, <2>4 DEF APL!Deallocate
    <2> QED BY <2>5 DEF APL!Next

  <1>D. ASSUME CFinish PROVE [APL!Next]_(APL!vars)
    <2> USE <1>D DEF CFinish
    <2>a. /\ ~complete
          /\ \A s \in Seats : ReadA(s) /= NULL => ReadE(s) /= NULL
          /\ complete' = TRUE
          /\ e_alloc' = e_alloc
          /\ e_eff' = e_eff
      OBVIOUS
    <2>1. AllocView' = AllocView   BY <2>a DEF AllocView, ReadA
    <2>2. EffView' = EffView       BY <2>a DEF EffView, ReadE
    <2>3. \A s \in Seats : AllocView[s] /= NULL => EffView[s] /= NULL
      BY <2>a DEF AllocView, EffView
    <2>4. APL!Finish
      BY <2>a, <2>1, <2>2, <2>3 DEF APL!Finish
    <2> QED BY <2>4 DEF APL!Next

  <1>E. CASE Next
    BY <1>A, <1>B, <1>C, <1>D, <1>E DEF Next
  <1> QED BY <1>0, <1>E

THEOREM Refinement == Spec => APL!Spec
  <1>1. Init => APL!Init                              BY InitRefines
  <1>2. Inv /\ [Next]_vars => [APL!Next]_(APL!vars)   BY NextRefines
  <1>3. Spec => []Inv                                 BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, APL!Spec

THEOREM RefinementOriginal == Spec => ActuationPassRefinement
  BY Refinement DEF ActuationPassRefinement

====
