---- MODULE ResourceRegistry_Proof ----
(* TLAPS proof of ResourceRegistry safety. UniqueMapping requires reasoning
   about Cardinality of sets of entries with a given key. *)
EXTENDS ResourceRegistry, Naturals, FiniteSets, FiniteSetTheorems, TLAPS

Inv == TypeInvariant /\ UniqueMapping

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant   BY DEF Init, TypeInvariant
  <1>2. UniqueMapping
    <2> SUFFICES ASSUME NEW k \in Keys
                 PROVE Cardinality({v \in Values : <<k, v>> \in entries}) <= 1
      BY DEF UniqueMapping
    <2>1. {v \in Values : <<k, v>> \in entries} = {}
      BY DEF Init
    <2>2. Cardinality({}) = 0
      BY FS_EmptySet
    <2>3. Cardinality({v \in Values : <<k, v>> \in entries}) = 0
      BY <2>1, <2>2
    <2> QED  BY <2>3
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, UniqueMapping
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE \E k \in Keys, v \in Values : Register(k, v)
    <2> SUFFICES ASSUME NEW k \in Keys, NEW v \in Values, Register(k, v)
                 PROVE Inv'
      BY <1>A
    <2>a. entries' = {e \in entries : e[1] /= k} \cup {<<k, v>>}
      BY DEF Register
    <2>1. TypeInvariant'
      <3>1. entries' \subseteq (Keys \X Values)
        BY <2>a
      <3> QED  BY <3>1 DEF TypeInvariant
    <2>2. UniqueMapping'
      <3> SUFFICES ASSUME NEW kk \in Keys
                   PROVE Cardinality({vv \in Values : <<kk, vv>> \in entries'}) <= 1
        BY DEF UniqueMapping
      <3>A. CASE kk = k
        <4>1. {vv \in Values : <<kk, vv>> \in entries'} = {v}
          BY <2>a, <3>A
        <4>2. Cardinality({v}) = 1
          BY FS_Singleton
        <4> QED  BY <4>1, <4>2
      <3>B. CASE kk /= k
        <4>1. {vv \in Values : <<kk, vv>> \in entries'} = {vv \in Values : <<kk, vv>> \in entries}
          BY <2>a, <3>B
        <4>2. Cardinality({vv \in Values : <<kk, vv>> \in entries}) <= 1
          OBVIOUS
        <4> QED  BY <4>1, <4>2
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2
  <1>B. CASE \E k \in Keys : Deregister(k)
    <2> SUFFICES ASSUME NEW k \in Keys, Deregister(k) PROVE Inv'
      BY <1>B
    <2>a. entries' = {e \in entries : e[1] /= k}
      BY DEF Deregister
    <2>1. TypeInvariant'
      <3>1. entries' \subseteq (Keys \X Values)
        BY <2>a
      <3> QED  BY <3>1 DEF TypeInvariant
    <2>2. UniqueMapping'
      <3> SUFFICES ASSUME NEW kk \in Keys
                   PROVE Cardinality({vv \in Values : <<kk, vv>> \in entries'}) <= 1
        BY DEF UniqueMapping
      <3>A. CASE kk = k
        <4>1. {vv \in Values : <<kk, vv>> \in entries'} = {}
          BY <2>a, <3>A
        <4>2. Cardinality({}) = 0
          BY FS_EmptySet
        <4>3. Cardinality({vv \in Values : <<kk, vv>> \in entries'}) = 0
          BY <4>1, <4>2
        <4> QED  BY <4>3
      <3>B. CASE kk /= k
        <4>1. {vv \in Values : <<kk, vv>> \in entries'} = {vv \in Values : <<kk, vv>> \in entries}
          BY <2>a, <3>B
        <4>2. Cardinality({vv \in Values : <<kk, vv>> \in entries}) <= 1
          OBVIOUS
        <4> QED  BY <4>1, <4>2
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant     BY Safety, PTL DEF Inv
THEOREM UniqueMappingSafety == Spec => []UniqueMapping  BY Safety, PTL DEF Inv
====
