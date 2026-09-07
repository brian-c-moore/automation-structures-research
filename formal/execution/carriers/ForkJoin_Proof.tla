---- MODULE ForkJoin_Proof ----
(* Carrier-level TLAPS proof for ForkJoin. ReadyOnlyDone is the minimal
   reachable-state strengthening needed to rule out a stale ready flag while
   fork/join actions execute; the specified claims remain the four predicates
   named by the model. *)
EXTENDS ForkJoin, Naturals, FiniteSets, TLAPS

ReadyOnlyDone == output_ready => phase = "done"
Inv == TypeInvariant /\ BarrierCompleteness /\ OutputConsistency
       /\ PhaseOrdering /\ ReadyOnlyDone

LEMMA ChosenValueInDomain ==
    (CHOOSE v \in ValueDomain : TRUE) \in ValueDomain
  <1>1. \E v \in ValueDomain : TRUE  BY ValueDomainNonEmpty
  <1> QED  BY <1>1

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    <2>1. wstate \in [Workers -> WorkerStates]
      BY DEF Init, WorkerStates
    <2>2. wvalue \in [Workers -> ValueDomain]
      BY ChosenValueInDomain DEF Init
    <2>3. phase \in Phases /\ output_ready \in BOOLEAN
      BY DEF Init, Phases
    <2>4. output_snapshot \in [Workers -> ValueDomain]
      BY ChosenValueInDomain DEF Init
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF TypeInvariant
  <1>2. BarrierCompleteness  BY DEF Init, BarrierCompleteness
  <1>3. OutputConsistency  BY DEF Init, OutputConsistency
  <1>4. PhaseOrdering  BY DEF Init, PhaseOrdering
  <1>5. ReadyOnlyDone  BY DEF Init, ReadyOnlyDone
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

LEMMA StutterInv == Inv /\ UNCHANGED vars => Inv'
  <1> SUFFICES ASSUME Inv, UNCHANGED vars PROVE Inv'  OBVIOUS
  <1>1. wstate' = wstate /\ wvalue' = wvalue /\ phase' = phase
         /\ output_ready' = output_ready
         /\ output_snapshot' = output_snapshot
    BY DEF vars
  <1> QED  BY <1>1
    DEF Inv, TypeInvariant, BarrierCompleteness, OutputConsistency,
        PhaseOrdering, ReadyOnlyDone, AllComplete

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BarrierCompleteness, OutputConsistency,
              PhaseOrdering, ReadyOnlyDone
  <1>0. CASE UNCHANGED vars
    BY <1>0, StutterInv
  <1>A. CASE \E w \in Workers : StartWorker(w) \/ CompleteWorker(w)
    <2> SUFFICES ASSUME NEW w \in Workers,
                         StartWorker(w) \/ CompleteWorker(w)
                  PROVE Inv'
      BY <1>A
    <2>S. CASE StartWorker(w)
      <3>1. ~output_ready
        BY <2>S DEF StartWorker, ReadyOnlyDone
      <3>2. wstate' \in [Workers -> WorkerStates]
        BY <2>S DEF StartWorker, WorkerStates
      <3>3. wvalue' = wvalue /\ phase' = "fork"
             /\ output_ready' = output_ready
             /\ output_snapshot' = output_snapshot
        BY <2>S DEF StartWorker, vars
      <3>4. TypeInvariant'
        BY <3>2, <3>3 DEF Inv, TypeInvariant, WorkerStates, Phases
      <3>5. BarrierCompleteness' /\ OutputConsistency'
             /\ PhaseOrdering' /\ ReadyOnlyDone'
        BY <3>1, <3>3 DEF BarrierCompleteness, OutputConsistency,
                          PhaseOrdering, ReadyOnlyDone, AllComplete, Phases
      <3> QED  BY <3>4, <3>5 DEF Inv
    <2>C. CASE CompleteWorker(w)
      <3>1. ~output_ready
        BY <2>C DEF CompleteWorker, ReadyOnlyDone
      <3>2. wstate' \in [Workers -> WorkerStates]
        BY <2>C DEF CompleteWorker, WorkerStates
      <3>3. wvalue' \in [Workers -> ValueDomain]
        BY <2>C DEF CompleteWorker
      <3>4. phase' = "fork" /\ output_ready' = output_ready
             /\ output_snapshot' = output_snapshot
        BY <2>C DEF CompleteWorker, vars
      <3>5. TypeInvariant'
        BY <3>2, <3>3, <3>4 DEF Inv, TypeInvariant, WorkerStates, Phases
      <3>6. BarrierCompleteness' /\ OutputConsistency'
             /\ PhaseOrdering' /\ ReadyOnlyDone'
        BY <3>1, <3>4 DEF BarrierCompleteness, OutputConsistency,
                          PhaseOrdering, ReadyOnlyDone, AllComplete, Phases
      <3> QED  BY <3>5, <3>6 DEF Inv
    <2> QED  BY <2>S, <2>C
  <1>B. CASE Barrier
    <2>1. ~output_ready
      BY <1>B DEF Barrier, ReadyOnlyDone
    <2>2. AllComplete
      BY <1>B DEF Barrier
    <2>3. phase' = "join" /\ wstate' = wstate /\ wvalue' = wvalue
           /\ output_ready' = output_ready
           /\ output_snapshot' = output_snapshot
      BY <1>B DEF Barrier, vars
    <2> QED  BY <2>1, <2>2, <2>3
      DEF Inv, TypeInvariant, BarrierCompleteness, OutputConsistency,
          PhaseOrdering, ReadyOnlyDone, AllComplete, Phases
  <1>C. CASE ProduceOutput
    <2>1. AllComplete
      BY <1>C DEF ProduceOutput, PhaseOrdering
    <2>2. output_snapshot' = wvalue /\ output_ready' = TRUE
           /\ phase' = "done" /\ wstate' = wstate /\ wvalue' = wvalue
      BY <1>C DEF ProduceOutput, vars
    <2> QED  BY <2>1, <2>2
      DEF Inv, TypeInvariant, BarrierCompleteness, OutputConsistency,
          PhaseOrdering, ReadyOnlyDone, AllComplete, Phases
  <1>D. CASE DoneStuttering
    BY <1>D, StutterInv DEF DoneStuttering
  <1>E. CASE Next
    BY <1>E, <1>A, <1>B, <1>C, <1>D DEF Next
  <1> QED  BY <1>0, <1>E

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv
THEOREM BarrierCompletenessSafety == Spec => []BarrierCompleteness
  BY Safety, PTL DEF Inv
THEOREM OutputConsistencySafety == Spec => []OutputConsistency
  BY Safety, PTL DEF Inv
THEOREM PhaseOrderingSafety == Spec => []PhaseOrdering
  BY Safety, PTL DEF Inv
====
