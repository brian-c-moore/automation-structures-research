---- MODULE SamplerFromActuationBudget_Proof ----
(***************************************************************************
  TLAPS proof of the concept-tier Sampler minimality refinement.

  Discharges, unbounded and parametric:

      Refinement == Spec => SMP!Spec

  i.e. every behaviour of the ActuationPass + Budget construction is a
  Sampler behaviour. This lifts the TLC-bounded PROPERTY SamplerRefinement to
  the parametric tier.

  Two load-bearing steps, one per obligation.

  1. THE LEDGER COUPLING, carried in the inductive invariant:
     Cardinality(Selected) = b_allocated. It is what makes Budget's
     allocation ledger BE the sample count, so Budget's own ceiling supplies
     BoundedSample. Preserving it across a draw is the finite-cardinality
     step (FS_AddElement over a fresh element), and the freshness comes from
     the COMPONENT's own guard `effects[i] = NULL` rather than from anything
     this construction adds.

  2. SUPPORT CONSISTENCY IS NEVER PROVED HERE, and that is the result. The
     target's SupportConsistency is ActuationPass's own ActuationScope
     under NULL <- 0, and the component proves it of its own actions
     (ActuationPass_Proof.ActuationScopeSafety). This construction uses
     `Act!Actuate` and `Act!Deallocate` verbatim, so the refinement obtains
     it without an inductive invariant of its own: what the proof below
     carries for the draw and the withdrawal is only typing, the ledger, and
     the projection identity Selected' = Selected \cup {i}. Compare
     QualityHierarchyFromGraphRegistry_Proof, where the construction had to
     carry UniqueParentOf itself because no component supplied it -- the
     same distinction, showing up as a proof obligation in the other
     direction.

  Contracts: SampleSize and MaxProb any naturals, Items any finite set --
  EXACTLY Sampler's own three (SampleSizeType, MaxProbType,
  ItemsFinite), which are also Sampler_Proof's three. The
  reduction costs the target no precondition it did not already have.
  ActuationPass_Proof carries no module-level ASSUME at all, and
  Budget's Capacity is bound to SampleSize.
 ***************************************************************************)
EXTENDS SamplerFromActuationBudget, FiniteSetTheorems, TLAPS

ASSUME SampleSizeAss == SampleSize \in Nat
ASSUME MaxProbAss == MaxProb \in Nat
ASSUME ItemsFinite == IsFiniteSet(Items)

Inv == TypeInvariant

(*-------------------------------------------------------------------------*)
(* The value-domain identity that makes the mapping type-correct: the       *)
(* component's Resources \cup {NULL} IS the target's probability range,     *)
(* with 0 as the out-of-support sentinel.                                   *)
(*-------------------------------------------------------------------------*)
LEMMA DomainSplit == (1..MaxProb) \cup {0} = 0..MaxProb
  BY MaxProbAss

LEMMA SelectedTyped == Selected \subseteq Items
  BY DEF Selected, Act!Actuated

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                         *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>a. /\ a_alloc \in [Items -> (1..MaxProb) \cup {0}]
        /\ a_eff = [s \in Items |-> 0]
        /\ a_complete = FALSE
    BY DEF Init, Act!Init
  <1>b. /\ b_capacity = SampleSize
        /\ b_allocated = 0
        /\ b_reserved = 0
        /\ b_pending = 0
    BY DEF Init, Bgt!Init
  <1>1. Act!TypeInvariant
    BY <1>a, MaxProbAss DEF Act!TypeInvariant
  <1>2. Selected = {}
    <2> SUFFICES ASSUME NEW s \in Selected PROVE FALSE  OBVIOUS
    <2>1. s \in Items /\ a_eff[s] /= 0   BY DEF Selected, Act!Actuated
    <2>2. a_eff[s] = 0                    BY <1>a, <2>1
    <2> QED  BY <2>1, <2>2
  <1>3. Cardinality(Selected) = b_allocated
    <2>1. Cardinality({}) = 0   BY FS_EmptySet
    <2> QED  BY <1>2, <2>1, <1>b
  <1> QED  BY <1>1, <1>3, <1>b, SampleSizeAss DEF Inv, TypeInvariant

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.                *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1>c. /\ a_alloc \in [Items -> (1..MaxProb) \cup {0}]
        /\ a_eff \in [Items -> (1..MaxProb) \cup {0}]
        /\ a_complete \in BOOLEAN
        /\ b_capacity = SampleSize
        /\ b_allocated \in 0..SampleSize
        /\ b_reserved = 0
        /\ b_pending = 0
        /\ Cardinality(Selected) = b_allocated
    BY DEF Inv, TypeInvariant, Act!TypeInvariant
  <1>f. IsFiniteSet(Selected)
    BY SelectedTyped, ItemsFinite, FS_Subset

  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<a_alloc, a_eff, a_complete,
                      b_capacity, b_allocated, b_reserved, b_pending>>
      BY <1>0 DEF vars
    <2>2. Selected' = Selected   BY <2>1 DEF Selected, Act!Actuated
    <2> QED  BY <2>1, <2>2, <1>c
         DEF Inv, TypeInvariant, Act!TypeInvariant

  \* ---- the draw: the component's fused read-and-mark + Budget's ledger ----
  <1>D. CASE \E i \in Items : CDraw(i)
    <2> SUFFICES ASSUME NEW i \in Items, CDraw(i) PROVE Inv'
      BY <1>D
    <2>a. /\ a_eff[i] = 0
          /\ a_alloc[i] /= 0
          /\ a_eff' = [a_eff EXCEPT ![i] = a_alloc[i]]
          /\ UNCHANGED <<a_alloc, a_complete>>
      BY DEF CDraw, Act!Actuate
    <2>b. /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
          /\ b_allocated' = b_allocated + 1
          /\ UNCHANGED <<b_capacity, b_reserved, b_pending>>
      BY DEF CDraw
    <2>1. a_eff' \in [Items -> (1..MaxProb) \cup {0}]
      BY <2>a, <1>c
    <2>2. Act!TypeInvariant'
      BY <2>1, <2>a, <1>c DEF Act!TypeInvariant
    <2>3. b_allocated' \in 0..SampleSize
      BY <2>a, <2>b, <1>c, SampleSizeAss
    \* The projection identity: the mark lands on exactly one fresh item.
    <2>4. Selected' = Selected \cup {i}
      <3> SUFFICES ASSUME NEW k \in Items
                   PROVE  (a_eff'[k] /= 0) <=> (a_eff[k] /= 0 \/ k = i)
        BY DEF Selected, Act!Actuated
      <3>1. CASE k = i
        <4>1. a_eff'[k] = a_alloc[i]   BY <2>a, <3>1, <1>c
        <4> QED  BY <4>1, <2>a, <3>1
      <3>2. CASE k /= i
        <4>1. a_eff'[k] = a_eff[k]     BY <2>a, <3>2, <1>c
        <4> QED  BY <4>1, <3>2
      <3> QED  BY <3>1, <3>2
    <2>5. i \notin Selected
      BY <2>a DEF Selected, Act!Actuated
    <2>6. Cardinality(Selected') = Cardinality(Selected) + 1
      BY <2>4, <2>5, <1>f, FS_AddElement
    <2>7. Cardinality(Selected') = b_allocated'
      BY <2>6, <2>b, <1>c
    <2> QED  BY <2>2, <2>3, <2>7, <2>b, <1>c DEF Inv, TypeInvariant

  \* ---- the withdrawal: the component's own Deallocate, verbatim ----
  <1>Z. CASE \E i \in Items : CZero(i)
    <2> SUFFICES ASSUME NEW i \in Items, CZero(i) PROVE Inv'
      BY <1>Z
    <2>a. /\ a_eff[i] = 0
          /\ a_alloc[i] /= 0
          /\ a_alloc' = [a_alloc EXCEPT ![i] = 0]
          /\ UNCHANGED <<a_eff, a_complete>>
      BY DEF CZero, Act!Deallocate
    <2>b. UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending>>
      BY DEF CZero
    <2>1. a_alloc' \in [Items -> (1..MaxProb) \cup {0}]
      BY <2>a, <1>c
    <2>2. Act!TypeInvariant'
      BY <2>1, <2>a, <1>c DEF Act!TypeInvariant
    <2>3. Selected' = Selected
      BY <2>a DEF Selected, Act!Actuated
    <2> QED  BY <2>2, <2>3, <2>b, <1>c DEF Inv, TypeInvariant

  <1> QED  BY <1>0, <1>D, <1>Z DEF Next

(*-------------------------------------------------------------------------*)
(* Safety: the inductive invariant holds in every reachable state.          *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'   BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv

THEOREM BudgetSafetySafety == Spec => []BudgetSafety
  <1>1. Inv => BudgetSafety
    BY SampleSizeAss
       DEF Inv, TypeInvariant, BudgetSafety, Bgt!SafetyInvariant
  <1> QED  BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement: Init maps to SMP!Init, every step maps to a Sampler  *)
(* step or a Sampler stutter.                                          *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => SMP!Init
  <1> SUFFICES ASSUME Init PROVE SMP!Init  OBVIOUS
  <1>a. a_alloc \in [Items -> (1..MaxProb) \cup {0}]
    BY DEF Init, Act!Init
  <1>1. a_alloc \in [Items -> 0..MaxProb]
    BY <1>a, DomainSplit
  <1>2. Selected = {}
    <2> SUFFICES ASSUME NEW s \in Selected PROVE FALSE  OBVIOUS
    <2>1. s \in Items /\ a_eff[s] /= 0   BY DEF Selected, Act!Actuated
    <2>2. a_eff = [s2 \in Items |-> 0]    BY DEF Init, Act!Init
    <2> QED  BY <2>1, <2>2
  <1> QED  BY <1>1, <1>2 DEF SMP!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [SMP!Next]_(SMP!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [SMP!Next]_(SMP!vars)  OBVIOUS
  <1>c. /\ a_alloc \in [Items -> (1..MaxProb) \cup {0}]
        /\ b_capacity = SampleSize
        /\ b_allocated \in 0..SampleSize
        /\ b_reserved = 0
        /\ b_pending = 0
        /\ Cardinality(Selected) = b_allocated
    BY DEF Inv, TypeInvariant, Act!TypeInvariant

  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<a_alloc, a_eff>>   BY <1>0 DEF vars
    <2>2. Selected' = Selected            BY <2>1 DEF Selected, Act!Actuated
    <2> QED  BY <2>1, <2>2 DEF SMP!vars

  <1>D. CASE \E i \in Items : CDraw(i)
    <2> SUFFICES ASSUME NEW i \in Items, CDraw(i)
                 PROVE  [SMP!Next]_(SMP!vars)
      BY <1>D
    <2>a. /\ a_eff[i] = 0
          /\ a_alloc[i] /= 0
          /\ a_eff' = [a_eff EXCEPT ![i] = a_alloc[i]]
          /\ UNCHANGED <<a_alloc, a_complete>>
      BY DEF CDraw, Act!Actuate
    <2>b. b_allocated + b_reserved + b_pending + 1 <= b_capacity
      BY DEF CDraw
    \* Budget's affordability test IS Sampler's room test, read through
    \* the ledger coupling.
    <2>1. SMP!Cardinality(Selected) < SampleSize
      BY <2>b, <1>c, SampleSizeAss DEF SMP!Cardinality, Cardinality
    \* The component's own guard IS the support guard.
    <2>2. a_alloc[i] > 0
      BY <2>a, <1>c
    <2>3. Selected' = Selected \cup {i}
      <3> SUFFICES ASSUME NEW k \in Items
                   PROVE  (a_eff'[k] /= 0) <=> (a_eff[k] /= 0 \/ k = i)
        BY DEF Selected, Act!Actuated
      <3>1. CASE k = i
        <4>1. a_eff'[k] = a_alloc[i]
          BY <2>a, <3>1, <1>c DEF Inv, TypeInvariant, Act!TypeInvariant
        <4> QED  BY <4>1, <2>a, <3>1
      <3>2. CASE k /= i
        <4>1. a_eff'[k] = a_eff[k]
          BY <2>a, <3>2 DEF Inv, TypeInvariant, Act!TypeInvariant
        <4> QED  BY <4>1, <3>2
      <3> QED  BY <3>1, <3>2
    <2>4. SMP!Sample
      BY <2>1, <2>2, <2>3, <2>a DEF SMP!Sample
    <2> QED  BY <2>4 DEF SMP!Next

  <1>Z. CASE \E i \in Items : CZero(i)
    <2> SUFFICES ASSUME NEW i \in Items, CZero(i)
                 PROVE  [SMP!Next]_(SMP!vars)
      BY <1>Z
    <2>a. /\ a_eff[i] = 0
          /\ a_alloc' = [a_alloc EXCEPT ![i] = 0]
          /\ UNCHANGED <<a_eff, a_complete>>
      BY DEF CZero, Act!Deallocate
    <2>1. i \notin Selected
      BY <2>a DEF Selected, Act!Actuated
    <2>2. Selected' = Selected
      BY <2>a DEF Selected, Act!Actuated
    <2>3. SMP!Zero(i)
      BY <2>1, <2>2, <2>a DEF SMP!Zero
    <2> QED  BY <2>3 DEF SMP!Next

  <1> QED  BY <1>0, <1>D, <1>Z DEF Next

(*-------------------------------------------------------------------------*)
(* The main result: the construction refines Sampler, unbounded.       *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => SMP!Spec
  <1>1. Init => SMP!Init                              BY InitRefines
  <1>2. Inv /\ [Next]_vars => [SMP!Next]_(SMP!vars)   BY NextRefines
  <1>3. Spec => []Inv                                 BY Safety
  <1> QED  BY <1>1, <1>2, <1>3, PTL DEF Spec, SMP!Spec

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => SamplerRefinement
  BY Refinement DEF SamplerRefinement

====
