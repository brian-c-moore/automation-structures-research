---- MODULE ForkJoinRefinesStepGraph_Proof ----
(* TLAPS proof of ForkJoinRefinesStepGraph.
   Proves TypeInvariant + RefinementMapping.
   NoRunBeforePredecessors is TLAPS-proved parametrically below via one
   auxiliary inductive strengthening (JoinImpliesAllComplete: the sink
   phase is entered only after the barrier, so join/done implies every
   worker is complete).
   All three cfg invariants are TLAPS-proved for arbitrary WorkerIds
   disjoint from {Source, Sink}. *)
EXTENDS ForkJoinRefinesStepGraph, Naturals, FiniteSets, TLAPS

ASSUME WorkerIdsExt == WorkerIds # {} /\ Source \notin WorkerIds /\ Sink \notin WorkerIds

Inv == TypeInvariant /\ RefinementMapping

LEMMA SinkMapOfType == \A p \in Phases : SinkMapOf(p) \in SGStates
  <1> SUFFICES ASSUME NEW p \in Phases PROVE SinkMapOf(p) \in SGStates
    OBVIOUS
  <1>1. CASE p = "fork"   BY <1>1 DEF SinkMapOf, SGStates
  <1>2. CASE p = "join"   BY <1>2 DEF SinkMapOf, SGStates
  <1>3. CASE p = "done"   BY <1>3 DEF SinkMapOf, SGStates
  <1> QED  BY <1>1, <1>2, <1>3 DEF Phases

LEMMA WorkerMapOfType ==
    \A ws \in [WorkerIds -> WorkerStates], w \in WorkerIds :
        WorkerMapOf(ws, w) \in SGStates
  <1> SUFFICES ASSUME NEW ws \in [WorkerIds -> WorkerStates], NEW w \in WorkerIds
               PROVE WorkerMapOf(ws, w) \in SGStates
    OBVIOUS
  <1>1. CASE ws[w] = "ready"     BY <1>1 DEF WorkerMapOf, SGStates
  <1>2. CASE ws[w] = "running"   BY <1>2 DEF WorkerMapOf, SGStates
  <1>3. CASE ws[w] = "complete"  BY <1>3 DEF WorkerMapOf, SGStates
  <1> QED  BY <1>1, <1>2, <1>3 DEF WorkerStates

LEMMA ExpectedSGOfType ==
    \A p \in Phases, ws \in [WorkerIds -> WorkerStates] :
        ExpectedSGOf(p, ws) \in [SGNodes -> SGStates]
  <1> SUFFICES ASSUME NEW p \in Phases, NEW ws \in [WorkerIds -> WorkerStates]
               PROVE  ExpectedSGOf(p, ws) \in [SGNodes -> SGStates]
    OBVIOUS
  <1> SUFFICES ASSUME NEW n \in SGNodes PROVE ExpectedSGOf(p, ws)[n] \in SGStates
    BY DEF ExpectedSGOf
  <1>1. CASE n = Source
    BY <1>1 DEF ExpectedSGOf, SGStates
  <1>2. CASE n = Sink
    <2>0. Source # Sink           BY DEF Source, Sink
    <2>1. ExpectedSGOf(p, ws)[n] = SinkMapOf(p)
      BY <1>2, <2>0 DEF ExpectedSGOf
    <2> QED  BY <2>1, SinkMapOfType
  <1>3. CASE n \in WorkerIds
    <2>0. n # Source /\ n # Sink  BY <1>3, WorkerIdsExt DEF Source, Sink
    <2>1. ExpectedSGOf(p, ws)[n] = WorkerMapOf(ws, n)
      BY <2>0, <1>3 DEF ExpectedSGOf
    <2> QED  BY <2>1, <1>3, WorkerMapOfType
  <1> QED  BY <1>1, <1>2, <1>3, WorkerIdsExt DEF SGNodes

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    <2>1. wstate \in [WorkerIds -> WorkerStates]
      BY DEF Init, WorkerStates
    <2>2. phase \in Phases               BY DEF Init, Phases
    <2>3. output_ready \in BOOLEAN       BY DEF Init
    <2>4. sgstate \in [SGNodes -> SGStates]
      <3>1. "fork" \in Phases
        BY DEF Phases
      <3>2. [w \in WorkerIds |-> "ready"] \in [WorkerIds -> WorkerStates]
        BY DEF WorkerStates
      <3> QED  BY <3>1, <3>2, ExpectedSGOfType DEF Init
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF TypeInvariant
  <1>2. RefinementMapping
    \* Init sets sgstate = ExpectedSGOf("fork", initial wstate) directly,
    \* so RefinementMapping holds by inspection.
    BY DEF Init, RefinementMapping
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, RefinementMapping
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE \E w \in WorkerIds : StartWorker(w)
    <2> SUFFICES ASSUME NEW w \in WorkerIds, StartWorker(w) PROVE Inv'
      BY <1>1
    <2>a. wstate \in [WorkerIds -> WorkerStates]  BY DEF TypeInvariant
    <2>b. wstate' = [wstate EXCEPT ![w] = "running"]  BY DEF StartWorker
    <2>c. phase' = phase                          BY DEF StartWorker
    <2>d. output_ready' = output_ready            BY DEF StartWorker
    <2>e. sgstate' = ExpectedSGOf(phase, [wstate EXCEPT ![w] = "running"])
      BY DEF StartWorker
    <2>1. wstate' \in [WorkerIds -> WorkerStates]
      BY <2>a, <2>b DEF WorkerStates
    <2>2. phase' \in Phases
      BY <2>c DEF TypeInvariant
    <2>3. output_ready' \in BOOLEAN
      BY <2>d DEF TypeInvariant
    <2>x. phase \in Phases                         BY DEF TypeInvariant
    <2>y. [wstate EXCEPT ![w] = "running"] \in [WorkerIds -> WorkerStates]
      BY <2>1, <2>b
    <2>4. sgstate' \in [SGNodes -> SGStates]
      BY <2>x, <2>y, <2>e, ExpectedSGOfType
    <2>5. RefinementMapping'
      BY <2>b, <2>c, <2>e
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>2. CASE \E w \in WorkerIds : CompleteWorker(w)
    <2> SUFFICES ASSUME NEW w \in WorkerIds, CompleteWorker(w) PROVE Inv'
      BY <1>2
    <2>a. wstate \in [WorkerIds -> WorkerStates]  BY DEF TypeInvariant
    <2>b. wstate' = [wstate EXCEPT ![w] = "complete"]  BY DEF CompleteWorker
    <2>c. phase' = phase                          BY DEF CompleteWorker
    <2>d. output_ready' = output_ready            BY DEF CompleteWorker
    <2>e. sgstate' = ExpectedSGOf(phase, [wstate EXCEPT ![w] = "complete"])
      BY DEF CompleteWorker
    <2>1. wstate' \in [WorkerIds -> WorkerStates]
      BY <2>a, <2>b DEF WorkerStates
    <2>2. phase' \in Phases
      BY <2>c DEF TypeInvariant
    <2>3. output_ready' \in BOOLEAN
      BY <2>d DEF TypeInvariant
    <2>x. phase \in Phases                         BY DEF TypeInvariant
    <2>y. [wstate EXCEPT ![w] = "complete"] \in [WorkerIds -> WorkerStates]
      BY <2>1, <2>b
    <2>4. sgstate' \in [SGNodes -> SGStates]
      BY <2>x, <2>y, <2>e, ExpectedSGOfType
    <2>5. RefinementMapping'
      BY <2>b, <2>c, <2>e
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>3. CASE Barrier
    <2>a. wstate \in [WorkerIds -> WorkerStates]  BY DEF TypeInvariant
    <2>b. wstate' = wstate                         BY <1>3 DEF Barrier
    <2>c. phase' = "join"                          BY <1>3 DEF Barrier
    <2>d. output_ready' = output_ready             BY <1>3 DEF Barrier
    <2>e. sgstate' = ExpectedSGOf("join", wstate) BY <1>3 DEF Barrier
    <2>x. "join" \in Phases                       BY DEF Phases
    <2>1. wstate' \in [WorkerIds -> WorkerStates]  BY <2>a, <2>b
    <2>2. phase' \in Phases                        BY <2>c DEF Phases
    <2>3. output_ready' \in BOOLEAN                BY <2>d DEF TypeInvariant
    <2>4. sgstate' \in [SGNodes -> SGStates]
      BY <2>a, <2>x, <2>e, ExpectedSGOfType
    <2>5. RefinementMapping'
      BY <2>b, <2>c, <2>e
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>4. CASE ProduceOutput
    <2>a. wstate \in [WorkerIds -> WorkerStates]  BY DEF TypeInvariant
    <2>b. wstate' = wstate                         BY <1>4 DEF ProduceOutput
    <2>c. phase' = "done"                          BY <1>4 DEF ProduceOutput
    <2>d. output_ready' = TRUE                     BY <1>4 DEF ProduceOutput
    <2>e. sgstate' = ExpectedSGOf("done", wstate) BY <1>4 DEF ProduceOutput
    <2>1. wstate' \in [WorkerIds -> WorkerStates]  BY <2>a, <2>b
    <2>2. phase' \in Phases                        BY <2>c DEF Phases
    <2>3. output_ready' \in BOOLEAN                BY <2>d
    <2>x. "done" \in Phases                       BY DEF Phases
    <2>4. sgstate' \in [SGNodes -> SGStates]
      BY <2>a, <2>x, <2>e, ExpectedSGOfType
    <2>5. RefinementMapping'
      BY <2>b, <2>c, <2>e
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>5. CASE phase = "done" /\ UNCHANGED vars
    BY <1>5 DEF vars
  <1>X. CASE Next
    BY <1>X, <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant       BY Safety, PTL DEF Inv
THEOREM RefinementSafety == Spec => []RefinementMapping  BY Safety, PTL DEF Inv

(* ================================================================== *)
(* NoRunBeforePredecessors. Inv2 adds the one auxiliary strengthening  *)
(* to Inv and reuses InitInv/NextInv for the Inv conjunct; the         *)
(* structural invariant is then a pointwise consequence of Inv2.       *)
(* ================================================================== *)

\* The sink phase is reachable only through the barrier: whenever the
\* phase is "join" or "done", every worker has completed.
JoinImpliesAllComplete == phase \in {"join", "done"} => AllComplete

Inv2 == Inv /\ JoinImpliesAllComplete

LEMMA InitInv2 == Init => Inv2
  <1> SUFFICES ASSUME Init PROVE Inv2  OBVIOUS
  <1>1. Inv  BY InitInv
  <1>2. JoinImpliesAllComplete
    BY DEF Init, JoinImpliesAllComplete
  <1> QED  BY <1>1, <1>2 DEF Inv2

LEMMA NextInv2 == Inv2 /\ [Next]_vars => Inv2'
  <1> SUFFICES ASSUME Inv2, [Next]_vars PROVE Inv2'  OBVIOUS
  <1>I. Inv'
    BY NextInv DEF Inv2
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>I DEF vars, Inv2, JoinImpliesAllComplete, AllComplete
  <1>1. CASE \E w \in WorkerIds : StartWorker(w)
    <2> SUFFICES ASSUME NEW w \in WorkerIds, StartWorker(w) PROVE Inv2'
      BY <1>1
    <2>1. phase' = phase /\ phase = "fork"
      BY DEF StartWorker
    <2> QED  BY <1>I, <2>1 DEF Inv2, JoinImpliesAllComplete
  <1>2. CASE \E w \in WorkerIds : CompleteWorker(w)
    <2> SUFFICES ASSUME NEW w \in WorkerIds, CompleteWorker(w) PROVE Inv2'
      BY <1>2
    <2>1. phase' = phase /\ phase = "fork"
      BY DEF CompleteWorker
    <2> QED  BY <1>I, <2>1 DEF Inv2, JoinImpliesAllComplete
  <1>3. CASE Barrier
    <2>1. AllComplete /\ wstate' = wstate
      BY <1>3 DEF Barrier
    <2> QED  BY <1>I, <2>1 DEF Inv2, JoinImpliesAllComplete, AllComplete
  <1>4. CASE ProduceOutput
    <2>1. phase = "join" /\ wstate' = wstate
      BY <1>4 DEF ProduceOutput
    <2>2. AllComplete
      BY <2>1 DEF Inv2, JoinImpliesAllComplete
    <2> QED  BY <1>I, <2>1, <2>2 DEF Inv2, JoinImpliesAllComplete, AllComplete
  <1>5. CASE phase = "done" /\ UNCHANGED vars
    BY <1>5, <1>I DEF vars, Inv2, JoinImpliesAllComplete, AllComplete
  <1>X. CASE Next
    BY <1>X, <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety2 == Spec => []Inv2
  <1>1. Init => Inv2                 BY InitInv2
  <1>2. Inv2 /\ [Next]_vars => Inv2'  BY NextInv2
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

\* Stated at the top level rather than inline, and cited from
\* MappedNoRun's proof.
LEMMA SourceNeqSink == Source # Sink
  BY DEF Source, Sink

\* Pointwise: any mapped state whose phase honors the barrier fact
\* satisfies StepGraph eligibility on the star topology.
LEMMA MappedNoRun ==
    \A p \in Phases, ws \in [WorkerIds -> WorkerStates] :
        (p \in {"join", "done"} => \A u \in WorkerIds : ws[u] = "complete") =>
        \A n \in SGNodes :
            ExpectedSGOf(p, ws)[n] \in {"Running", "Completed"} =>
                \A q \in PredecessorsOf(n) : ExpectedSGOf(p, ws)[q] = "Completed"
  <1> SUFFICES ASSUME NEW p \in Phases, NEW ws \in [WorkerIds -> WorkerStates],
                      p \in {"join", "done"} => \A u \in WorkerIds : ws[u] = "complete",
                      NEW n \in SGNodes,
                      ExpectedSGOf(p, ws)[n] \in {"Running", "Completed"},
                      NEW q \in PredecessorsOf(n)
               PROVE  ExpectedSGOf(p, ws)[q] = "Completed"
    OBVIOUS
  <1>e. <<q, n>> \in SGEdges /\ q \in SGNodes
    BY DEF PredecessorsOf
  <1>d. Source # Sink
    BY SourceNeqSink
  <1>A. CASE n = Source
    \* No SGEdge targets Source, so the predecessor set is empty.
    <2>1. \E w \in WorkerIds : <<q, n>> = <<Source, w>> \/ <<q, n>> = <<w, Sink>>
      BY <1>e DEF SGEdges
    <2> QED  BY <1>A, <2>1, <1>d, WorkerIdsExt
  <1>B. CASE n \in WorkerIds
    <2>1. q = Source
      BY <1>B, <1>e, WorkerIdsExt DEF SGEdges
    <2> QED  BY <2>1, <1>d, WorkerIdsExt DEF ExpectedSGOf, SGNodes
  <1>C. CASE n = Sink
    <2>1. q \in WorkerIds
      BY <1>C, <1>e, <1>d, WorkerIdsExt DEF SGEdges
    <2>2. ExpectedSGOf(p, ws)[n] = SinkMapOf(p)
      BY <1>C, <1>d DEF ExpectedSGOf, SGNodes
    <2>3. p \in {"join", "done"}
      <3>1. CASE p = "fork"
        BY <3>1, <2>2 DEF SinkMapOf
      <3>2. CASE p = "join"  BY <3>2
      <3>3. CASE p = "done"  BY <3>3
      <3> QED  BY <3>1, <3>2, <3>3 DEF Phases
    <2>4. ws[q] = "complete"
      BY <2>1, <2>3
    <2>5. ExpectedSGOf(p, ws)[q] = WorkerMapOf(ws, q)
      BY <2>1, WorkerIdsExt DEF ExpectedSGOf, SGNodes
    <2> QED  BY <2>4, <2>5 DEF WorkerMapOf
  <1> QED  BY <1>A, <1>B, <1>C DEF SGNodes

THEOREM NoRunBeforePredecessorsSafety == Spec => []NoRunBeforePredecessors
  <1>1. Inv2 => NoRunBeforePredecessors
    <2> SUFFICES ASSUME Inv2 PROVE NoRunBeforePredecessors
      OBVIOUS
    <2>1. phase \in Phases /\ wstate \in [WorkerIds -> WorkerStates]
      BY DEF Inv2, Inv, TypeInvariant
    <2>2. sgstate = ExpectedSGOf(phase, wstate)
      BY DEF Inv2, Inv, RefinementMapping
    <2>3. phase \in {"join", "done"} => \A u \in WorkerIds : wstate[u] = "complete"
      BY DEF Inv2, JoinImpliesAllComplete, AllComplete
    <2> QED
      BY <2>1, <2>2, <2>3, MappedNoRun DEF NoRunBeforePredecessors
  <1> QED  BY Safety2, <1>1, PTL
====
