---- MODULE ActuationPass_Proof ----
(* TLAPS safety proof for ActuationPass.

   Inv is TypeInvariant /\ EffectFidelity /\ PassCompleteness. ActuationScope
   is proved as a COROLLARY of EffectFidelity: an effect record that always
   agrees with the live allocation cannot name an unallocated seat. Actuated is
   derived as a projection rather than held as a separate marker beside
   `effects`, which would make the two mutually derivable.

   No module-level ASSUME: the proof is parametric in Seats, Resources and
   NULL, and in particular does NOT need NULL \notin Resources.               *)
EXTENDS ActuationPass, FiniteSets, TLAPS

Inv == TypeInvariant /\ EffectFidelity /\ PassCompleteness

(* ------------------------------------------------------------------ *)
(* ActuationScope as a state-level consequence of EffectFidelity.       *)
(* ------------------------------------------------------------------ *)
LEMMA ScopeFromFidelity == EffectFidelity => ActuationScope
  BY DEF EffectFidelity, ActuationScope, Actuated

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1> USE DEF Init
  <1>1. TypeInvariant     BY DEF TypeInvariant
  <1>2. EffectFidelity    BY DEF EffectFidelity
  <1>3. PassCompleteness  BY DEF PassCompleteness
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, EffectFidelity, PassCompleteness

  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars

  \* ---- the pass: read the allocation and apply the operation, fused ----
  <1>1. ASSUME NEW s \in Seats, Actuate(s) PROVE Inv'
    <2> USE <1>1 DEF Actuate
    <2>a. allocation' = allocation                            OBVIOUS
    <2>b. complete' = complete                                OBVIOUS
    <2>c. effects' = [effects EXCEPT ![s] = allocation[s]]     OBVIOUS
    <2>d. allocation[s] \in Resources \cup {NULL}              OBVIOUS
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>c, <2>d
    <2>2. EffectFidelity'
      <3> SUFFICES ASSUME NEW t \in Seats, effects'[t] /= NULL
                   PROVE  effects'[t] = allocation'[t]
        BY DEF EffectFidelity
      <3>1. CASE t = s
        <4>1. effects'[t] = allocation[s]   BY <2>c, <3>1
        <4> QED  BY <4>1, <2>a, <3>1
      <3>2. CASE t /= s
        <4>1. effects'[t] = effects[t]      BY <2>c, <3>2
        <4> QED  BY <4>1, <2>a
      <3> QED  BY <3>1, <3>2
    <2>3. PassCompleteness'
      <3>1. ~complete                        OBVIOUS
      <3> QED  BY <3>1, <2>b DEF PassCompleteness
    <2> QED  BY <2>1, <2>2, <2>3

  \* ---- the environment: a live allocation writer ----
  <1>2. ASSUME NEW s \in Seats, NEW r \in Resources, Allocate(s, r) PROVE Inv'
    <2> USE <1>2 DEF Allocate
    <2>a. effects' = effects                                  OBVIOUS
    <2>b. complete' = complete                                OBVIOUS
    <2>c. allocation' = [allocation EXCEPT ![s] = r]          OBVIOUS
    <2>d. allocation[s] = NULL                                OBVIOUS
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>c
    <2>2. EffectFidelity'
      <3> SUFFICES ASSUME NEW t \in Seats, effects'[t] /= NULL
                   PROVE  effects'[t] = allocation'[t]
        BY DEF EffectFidelity
      <3>0. effects[t] = allocation[t]       BY <2>a DEF EffectFidelity
      <3>1. CASE t = s
        \* the seat was unallocated, so by EffectFidelity it was unapplied;
        \* the antecedent is therefore contradictory.
        <4>1. effects[t] = NULL              BY <3>0, <2>d, <3>1
        <4> QED  BY <4>1, <2>a
      <3>2. CASE t /= s
        <4>1. allocation'[t] = allocation[t] BY <2>c, <3>2
        <4> QED  BY <4>1, <3>0, <2>a
      <3> QED  BY <3>1, <3>2
    <2>3. PassCompleteness'
      <3>1. ~complete                        OBVIOUS
      <3> QED  BY <3>1, <2>b DEF PassCompleteness
    <2> QED  BY <2>1, <2>2, <2>3

  <1>3. ASSUME NEW s \in Seats, Deallocate(s) PROVE Inv'
    <2> USE <1>3 DEF Deallocate
    <2>a. effects' = effects                                  OBVIOUS
    <2>b. complete' = complete                                OBVIOUS
    <2>c. allocation' = [allocation EXCEPT ![s] = NULL]       OBVIOUS
    <2>d. effects[s] = NULL                                   OBVIOUS
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>c
    <2>2. EffectFidelity'
      <3> SUFFICES ASSUME NEW t \in Seats, effects'[t] /= NULL
                   PROVE  effects'[t] = allocation'[t]
        BY DEF EffectFidelity
      <3>0. effects[t] = allocation[t]       BY <2>a DEF EffectFidelity
      <3>1. CASE t = s
        \* withdrawal is guarded by the pass's ownership: an applied seat
        \* cannot be deallocated, so the antecedent is contradictory.
        <4> QED  BY <2>d, <2>a, <3>1
      <3>2. CASE t /= s
        <4>1. allocation'[t] = allocation[t] BY <2>c, <3>2
        <4> QED  BY <4>1, <3>0, <2>a
      <3> QED  BY <3>1, <3>2
    <2>3. PassCompleteness'
      <3>1. ~complete                        OBVIOUS
      <3> QED  BY <3>1, <2>b DEF PassCompleteness
    <2> QED  BY <2>1, <2>2, <2>3

  \* ---- closure: the completeness check and the flag, fused ----
  <1>4. ASSUME Finish PROVE Inv'
    <2> USE <1>4 DEF Finish
    <2>a. allocation' = allocation                            OBVIOUS
    <2>b. effects' = effects                                  OBVIOUS
    <2>c. complete' = TRUE                                    OBVIOUS
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>c
    <2>2. EffectFidelity'
      BY <2>a, <2>b DEF EffectFidelity
    <2>3. PassCompleteness'
      BY <2>a, <2>b DEF PassCompleteness
    <2> QED  BY <2>1, <2>2, <2>3

  <1>5. CASE Next
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next
  <1> QED  BY <1>0, <1>5

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                   BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'    BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant             BY Safety, PTL DEF Inv
THEOREM EffectFidelitySafety == Spec => []EffectFidelity  BY Safety, PTL DEF Inv
THEOREM PassCompletenessSafety == Spec => []PassCompleteness
  BY Safety, PTL DEF Inv

\* ActuationScope as a corollary of EffectFidelity.
THEOREM ActuationScopeSafety == Spec => []ActuationScope
  <1>1. Spec => []Inv             BY Safety
  <1>2. Inv => ActuationScope     BY ScopeFromFidelity DEF Inv
  <1> QED  BY <1>1, <1>2, PTL
====
