---- MODULE ResourceRegistryFromGlue_Proof ----
(***************************************************************************
  Parametric TLAPS proof of the ResourceRegistry pure-glue refinement:

      Refinement == Spec => RR!Spec

  Under the substitution, Init, Next, and vars are the ResourceRegistry target
  with renamed variables, so refinement is definitional and requires no module
  assumption. TypeInvariant and MappedUniqueMapping are proved directly over
  store; no retained component supplies UniqueMapping.
 ***************************************************************************)
EXTENDS ResourceRegistryFromGlue, FiniteSetTheorems, TLAPS

Inv == TypeInvariant /\ MappedUniqueMapping

(*-------------------------------------------------------------------------*)
(* Safety of the construction's two configured invariants.                 *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant   BY DEF Init, TypeInvariant
  <1>2. MappedUniqueMapping
    <2> SUFFICES ASSUME NEW k \in Keys
                 PROVE Cardinality({v \in Values : <<k, v>> \in store}) <= 1
      BY DEF MappedUniqueMapping
    <2>1. {v \in Values : <<k, v>> \in store} = {}   BY DEF Init
    <2>2. Cardinality({}) = 0                         BY FS_EmptySet
    <2>3. 0 <= 1                                      OBVIOUS
    <2> QED  BY <2>1, <2>2, <2>3
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, MappedUniqueMapping
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE \E k \in Keys, v \in Values : Register(k, v)
    <2> SUFFICES ASSUME NEW k \in Keys, NEW v \in Values, Register(k, v)
                 PROVE  Inv'
      BY <1>A
    <2>a. store' = {e \in store : e[1] /= k} \cup {<<k, v>>}
      BY DEF Register
    <2>1. TypeInvariant'
      <3>1. store' \subseteq (Keys \X Values)   BY <2>a
      <3> QED  BY <3>1 DEF TypeInvariant
    <2>2. MappedUniqueMapping'
      <3> SUFFICES ASSUME NEW kk \in Keys
                   PROVE Cardinality({vv \in Values : <<kk, vv>> \in store'}) <= 1
        BY DEF MappedUniqueMapping
      <3>A. CASE kk = k
        <4>1. {vv \in Values : <<kk, vv>> \in store'} = {v}
          BY <2>a, <3>A
        <4>2. Cardinality({v}) = 1   BY FS_Singleton
        <4> QED  BY <4>1, <4>2
      <3>B. CASE kk /= k
        <4>1. {vv \in Values : <<kk, vv>> \in store'}
                = {vv \in Values : <<kk, vv>> \in store}
          BY <2>a, <3>B
        <4>2. Cardinality({vv \in Values : <<kk, vv>> \in store}) <= 1
          OBVIOUS
        <4> QED  BY <4>1, <4>2
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2
  <1>B. CASE \E k \in Keys : Deregister(k)
    <2> SUFFICES ASSUME NEW k \in Keys, Deregister(k) PROVE Inv'
      BY <1>B
    <2>a. store' = {e \in store : e[1] /= k}
      BY DEF Deregister
    <2>1. TypeInvariant'
      BY <2>a DEF TypeInvariant
    <2>2. MappedUniqueMapping'
      <3> SUFFICES ASSUME NEW kk \in Keys
                   PROVE Cardinality({vv \in Values : <<kk, vv>> \in store'}) <= 1
        BY DEF MappedUniqueMapping
      <3>A. CASE kk = k
        <4>1. {vv \in Values : <<kk, vv>> \in store'} = {}
          BY <2>a, <3>A
        <4>2. Cardinality({}) = 0   BY FS_EmptySet
        <4>3. 0 <= 1                OBVIOUS
        <4> QED  BY <4>1, <4>2, <4>3
      <3>B. CASE kk /= k
        <4>1. {vv \in Values : <<kk, vv>> \in store'}
                = {vv \in Values : <<kk, vv>> \in store}
          BY <2>a, <3>B
        <4>2. Cardinality({vv \in Values : <<kk, vv>> \in store}) <= 1
          OBVIOUS
        <4> QED  BY <4>1, <4>2
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

\* The construction's .cfg-checked invariant, now unbounded.
THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM MappedUniqueMappingSafety == Spec => []MappedUniqueMapping
  BY Safety, PTL DEF Inv

(*-------------------------------------------------------------------------*)
(* The refinement. No invariant is carried into it and none is needed: the  *)
(* substitution is a relabelling, so each step below is the target's own    *)
(* definition read under the new variable name.                            *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => RR!Init
  BY DEF Init, RR!Init

LEMMA NextRefines == [Next]_vars => [RR!Next]_(RR!vars)
  <1> SUFFICES ASSUME [Next]_vars PROVE [RR!Next]_(RR!vars)
    OBVIOUS
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<store>>
      BY <1>0 DEF vars
    <2> QED  BY <2>1 DEF RR!vars
  <1>X. CASE Next
    <2>A. CASE \E k \in Keys, v \in Values : Register(k, v)
      <3> SUFFICES ASSUME NEW k \in Keys, NEW v \in Values, Register(k, v)
                   PROVE  RR!Next
        BY <2>A
      <3>1. RR!Register(k, v)
        BY DEF Register, RR!Register
      <3> QED  BY <3>1 DEF RR!Next
    <2>B. CASE \E k \in Keys : Deregister(k)
      <3> SUFFICES ASSUME NEW k \in Keys, Deregister(k)
                   PROVE  RR!Next
        BY <2>B
      <3>1. RR!Deregister(k)
        BY DEF Deregister, RR!Deregister
      <3> QED  BY <3>1 DEF RR!Next
    <2> QED  BY <1>X, <2>A, <2>B DEF Next
  <1> QED  BY <1>0, <1>X

(*-------------------------------------------------------------------------*)
(* The state-only construction refines ResourceRegistry parametrically.     *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => RR!Spec
  <1>1. Init => RR!Init                                 BY InitRefines
  <1>2. [Next]_vars => [RR!Next]_(RR!vars)              BY NextRefines
  <1> QED  BY <1>1, <1>2, PTL DEF Spec, RR!Spec

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => ResourceRegistryRefinement
  BY Refinement DEF ResourceRegistryRefinement

====
