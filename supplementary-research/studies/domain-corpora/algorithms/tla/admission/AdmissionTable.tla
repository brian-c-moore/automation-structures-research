---- MODULE AdmissionTable ----
\* ====================================================================
\* ADMISSION TABLE
\*
\* Bridge between the structural-ordering axis (OrderingClassifier) and the
\* execution-modality axis.  For each (Ordering, Modality) cell the spec asks:
\* can a runtime implementing this modality execute a ComputationGraph
\* of this ordering using only that modality's native primitives?
\*
\* Predicted admission table:
\*
\*   Ordering | Seq  | FJ   | Step | Stream
\*   ---------+------+------+------+-------
\*   Linear   | PASS | VIO  | VIO  | VIO
\*   Tree     | PASS | PASS | PASS | PASS
\*   DAG      | PASS | PASS | PASS | PASS
\*   Cycles   | VIO  | VIO  | PASS | PASS
\*
\* CONSTANTS
\*   OrderingId in 1..4  (1=Linear  2=Tree  3=DAG  4=Cycles)
\*   ModalityId in 1..4  (1=Seq  2=FJ  3=Step  4=Stream)
\*
\* Each of the 16 .cfg files selects one cell.  The single .tla is
\* shared via the cfg-fallback convention.
\*
\* Self-contained: EXTENDS standard modules only — Naturals, Integers,
\* FiniteSets, Sequences.  No cross-directory EXTENDS.
\*
\* Modality disciplines mirrored from vendored EM specs:
\*   Seq   (Sequential.tla)  — one ready node at a time; single PC;
\*                             no iteration-to-fixed-point action.
\*   FJ    (ForkJoin.tla)    — fire all currently-eligible independent
\*                             nodes as a group; barrier before next
\*                             round; distinguishing move = group >=2.
\*   Step  (StepGraph.tla)   — node eligible when all predecessors
\*                             Done; distinguishing move = >=2 nodes
\*                             concurrently Running; iterative-round
\*                             re-eligibility action for Cycles.
\*   Stream (StreamGraph.tla)— per-record flow; distinguishing native
\*                             move = downstream active while upstream
\*                             still active on a fan or cycle topology
\*                             (per-record overlap on a graph node with
\*                             fan in/out or on a cyclic subgraph).
\*                             A simple pipeline chain (Linear) has no
\*                             fan or cycle, so the distinguishing move
\*                             can never fire there.
\*
\* INVARIANT  Admits:
\*   (complete => progressed) /\ (complete \/ CanNativeProgress)
\*   Conjunct 1: whenever execution completes, the modality's
\*               distinguishing native move must have fired at least
\*               once.  Catches Type-B violations (Linear/FJ, Step,
\*               Stream: completes but progressed=FALSE).
\*   Conjunct 2: if not yet complete, the modality must still be able
\*               to make native progress.  Catches Type-A violations
\*               (Cycles/Seq, Cycles/FJ: permanently stuck).
\*
\* CYCLES / Seq note (indirect-only finding):
\*   Native Seq has no iteration action.  After the explicit admission-check
\*   boundary, the Cycles graph violates conjunct 2 (no node is ready because
\*   the cycle has no source).  The boot step changes no graph/runtime state;
\*   it ensures the negative control is exercised by a transition instead of
\*   being a constant-false initial invariant.  This is the "indirect (only
\*   via added iteration machinery)" finding: Seq can execute cyclic
\*   computations only by augmenting its state machine with iteration
\*   infrastructure not present in its native primitive set.
\* ====================================================================
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS OrderingId, ModalityId
\* OrderingId : 1..4   1=Linear  2=Tree  3=DAG  4=Cycles
\* ModalityId : 1..4   1=Seq  2=FJ  3=Step  4=Stream

\* ----------------------------------------------------------------
\*  Graph definitions — one per OrderingId
\* ----------------------------------------------------------------
\* G_Nodes and G_Edges are the UNION over all four orderings,
\* gated by OrderingId.  TLC evaluates the constant-level operators
\* for the chosen OrderingId; the unused branches are never explored.

\* Linear: 1 -> 2 -> 3  (chain, 3 nodes)
Linear_Nodes == {1, 2, 3}
Linear_Edges == {<<1,2>>, <<2,3>>}

\* Tree: 1 -> 2, 1 -> 3  (fan-out, 3 nodes)
Tree_Nodes == {1, 2, 3}
Tree_Edges == {<<1,2>>, <<1,3>>}

\* DAG (diamond): 1 -> 2, 1 -> 3, 2 -> 4, 3 -> 4  (fan-out + fan-in)
DAG_Nodes == {1, 2, 3, 4}
DAG_Edges == {<<1,2>>, <<1,3>>, <<2,4>>, <<3,4>>}

\* Cycles: 1 -> 2 -> 3 -> 1  (3-cycle)
Cycles_Nodes == {1, 2, 3}
Cycles_Edges == {<<1,2>>, <<2,3>>, <<3,1>>}

G_Nodes ==
    IF OrderingId = 1 THEN Linear_Nodes
    ELSE IF OrderingId = 2 THEN Tree_Nodes
    ELSE IF OrderingId = 3 THEN DAG_Nodes
    ELSE Cycles_Nodes

G_Edges ==
    IF OrderingId = 1 THEN Linear_Edges
    ELSE IF OrderingId = 2 THEN Tree_Edges
    ELSE IF OrderingId = 3 THEN DAG_Edges
    ELSE Cycles_Edges

\* ----------------------------------------------------------------
\*  Graph structural operators  (mirror ComputationGraph.tla)
\* ----------------------------------------------------------------
Preds(n) == {p \in G_Nodes : <<p, n>> \in G_Edges}
Succs(n) == {s \in G_Nodes : <<n, s>> \in G_Edges}
InDeg(n) == Cardinality(Preds(n))
OutDeg(n) == Cardinality(Succs(n))

\* Bounded transitive closure for cycle detection.
ReachStep(S) == S \cup {b \in G_Nodes : \E a \in S : <<a, b>> \in G_Edges}
RECURSIVE Closure(_, _)
Closure(S, k) == IF k = 0 THEN S ELSE Closure(ReachStep(S), k - 1)
ReachFrom(n)  == Closure({m \in G_Nodes : <<n, m>> \in G_Edges}, Cardinality(G_Nodes))

HasCycle == \E n \in G_Nodes : n \in ReachFrom(n)

\* True when the graph contains at least one fan node (branch or merge).
HasFan == \E n \in G_Nodes : OutDeg(n) >= 2 \/ InDeg(n) >= 2

\* ----------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------
\* nstate  — per-node execution status
\*           "NotStarted" | "Running" | "Done"
\* progressed — TRUE once the modality's distinguishing native move fires
\* complete   — TRUE once all nodes are Done (via the appropriate
\*              completion rule for the modality/ordering combination)
\* iterDone   — for Step/Stream on Cycles: TRUE once the iterative-round
\*              or cycle-stream action has fired and driven all nodes Done

NodeStates == {"NotStarted", "Running", "Done"}

VARIABLES nstate, progressed, complete, checkPhase

vars == <<nstate, progressed, complete, checkPhase>>

TypeInvariant ==
    /\ nstate    \in [G_Nodes -> NodeStates]
    /\ progressed \in BOOLEAN
    /\ complete   \in BOOLEAN
    /\ checkPhase \in {"boot", "active"}

\* ----------------------------------------------------------------
\*  Derived predicates
\* ----------------------------------------------------------------
AllDone == \A n \in G_Nodes : nstate[n] = "Done"

\* A node is "ready" for sequential/step evaluation: all predecessors Done.
IsReady(n) == nstate[n] = "NotStarted" /\ \A p \in Preds(n) : nstate[p] = "Done"

\* All nodes that are currently ready.
ReadyNodes == {n \in G_Nodes : IsReady(n)}

\* Nodes that have been started (Running or Done).
StartedNodes == {n \in G_Nodes : nstate[n] # "NotStarted"}

\* Running nodes.
RunningNodes == {n \in G_Nodes : nstate[n] = "Running"}

\* ----------------------------------------------------------------
\*  SEQUENTIAL modality (ModalityId = 1)
\*
\*  Mirrors Sequential.tla: one ready node at a time, single PC.
\*  No iteration action — the machine halts when no node is ready.
\*  progressed: set on first sequential evaluation step (serial-step
\*  IS the native form of Seq; the distinguishing move is simply
\*  advancing the single PC to evaluate the next ready node).
\*
\*  PASS on Linear, Tree, DAG.
\*  VIO on Cycles: no node is ever ready (cycle has no source) →
\*  CanNativeProgress = FALSE before complete → conjunct 2 violated.
\*  [indirect (only via added iteration machinery) finding: Seq needs
\*   iteration infrastructure not in its native primitive set to handle
\*   cyclic dependencies.]
\* ----------------------------------------------------------------
SeqStep ==
    /\ ModalityId = 1
    /\ ~complete
    /\ \E n \in G_Nodes : IsReady(n)
    /\ LET n == CHOOSE x \in G_Nodes : IsReady(x)
       IN  nstate' = [nstate EXCEPT ![n] = "Done"]
    /\ progressed' = TRUE
    /\ complete'   = IF AllDone' THEN TRUE ELSE complete

\* For Seq: CanNativeProgress iff some node is ready (or already complete).
SeqCanProgress == ReadyNodes # {} \/ AllDone

\* ----------------------------------------------------------------
\*  FORK-JOIN modality (ModalityId = 2)
\*
\*  Mirrors ForkJoin.tla: fire all currently-eligible independent nodes
\*  as one group, then barrier.  "Eligible" = all predecessors Done.
\*  Distinguishing move: group size >= 2 (set progressed=TRUE).
\*  Degenerate move: group size = 1 (completes node, progressed unchanged).
\*  No iteration action.
\*
\*  PASS on Tree, DAG (at least one round fires a group of >=2).
\*  VIO on Linear: every eligible group has size 1 → progressed stays
\*    FALSE → complete=TRUE with progressed=FALSE → conjunct 1 violated.
\*  VIO on Cycles: no node is ever eligible (cycle has no source) →
\*    CanNativeProgress = FALSE before complete → conjunct 2 violated.
\* ----------------------------------------------------------------
\* FJ fires ALL currently ready nodes as a single group (barrier round).
FJFire ==
    /\ ModalityId = 2
    /\ ~complete
    /\ ReadyNodes # {}
    /\ nstate' = [n \in G_Nodes |->
                    IF nstate[n] = "NotStarted" /\ IsReady(n)
                    THEN "Done"
                    ELSE nstate[n]]
    /\ progressed' = IF Cardinality(ReadyNodes) >= 2
                     THEN TRUE
                     ELSE progressed
    /\ complete'   = IF \A n \in G_Nodes :
                          (nstate'[n] = "Done")
                     THEN TRUE
                     ELSE complete

FJCanProgress == ReadyNodes # {} \/ AllDone

\* ----------------------------------------------------------------
\*  STEP-GRAPH modality (ModalityId = 3)
\*
\*  Mirrors StepGraph.tla: a node becomes eligible (Ready) when all
\*  predecessors are Done; it then transitions NotStarted->Running->Done.
\*  Distinguishing move: >=2 nodes simultaneously Running → progressed.
\*  Iterative-round action (Cycles only): when no node is IsReady and
\*  not all nodes Done, reset all Done nodes to NotStarted to begin the
\*  next iteration round (fixed-point re-evaluation).  This action also
\*  sets progressed=TRUE (it IS the Step-native mechanism for cycles).
\*
\*  PASS on Tree, DAG (>=2 nodes can be concurrently Running).
\*  PASS on Cycles (iterative-round breaks the cycle deadlock).
\*  VIO on Linear: at most 1 node eligible at a time in a chain;
\*    iterative-round never fires (no cycle); progressed stays FALSE →
\*    conjunct 1 violated.
\* ----------------------------------------------------------------
\* Make ALL currently ready nodes Running simultaneously (synchronous round).
\* This is the key Step discipline: every node whose predecessors are Done
\* is promoted to Running in the same atomic step.  When >=2 nodes are ready
\* at the same time (Tree/DAG), they all go Running together → progressed.
\* When only 1 node is ever ready at a time (Linear chain), this never fires
\* a group of >=2 → progressed stays FALSE → invariant violated at completion.
StepBecomeReady ==
    /\ ModalityId = 3
    /\ ~complete
    /\ ReadyNodes # {}
    /\ nstate' = [n \in G_Nodes |->
                    IF IsReady(n) THEN "Running"
                    ELSE nstate[n]]
    /\ progressed' = IF Cardinality(ReadyNodes) >= 2
                     THEN TRUE
                     ELSE progressed
    /\ complete'   = complete

\* Complete a Running node.
StepComplete ==
    /\ ModalityId = 3
    /\ ~complete
    /\ \E n \in G_Nodes : nstate[n] = "Running"
    /\ \E n \in G_Nodes :
        /\ nstate[n] = "Running"
        /\ nstate' = [nstate EXCEPT ![n] = "Done"]
    /\ progressed' = progressed
    /\ complete'   = IF AllDone' THEN TRUE ELSE complete

\* Iterative-round: forcibly starts ONE node Running to break the
\* cyclic deadlock.  Fires only when the system is completely stuck
\* (no IsReady, no Running nodes, not AllDone) in a cyclic graph.
\* This is Step's cycle-native mechanism: it detects the cycle and
\* initializes a round by choosing an arbitrary entry point.
\* progressed is set TRUE because this action IS the distinguishing
\* Step primitive for cyclic graphs — no other modality has it.
StepIterativeRound ==
    /\ ModalityId = 3
    /\ ~complete
    /\ HasCycle
    /\ ReadyNodes   = {}
    /\ RunningNodes = {}
    /\ ~AllDone
    /\ \E n \in G_Nodes :
        /\ nstate[n] = "NotStarted"
        /\ nstate'   = [nstate EXCEPT ![n] = "Running"]
    /\ progressed' = TRUE
    /\ complete'   = complete

\* For Step: can progress if some node can become Ready, or a Running
\* node can complete, or iterative-round is applicable (stuck in cycle).
StepCanProgress ==
    \/ ReadyNodes   # {}
    \/ RunningNodes # {}
    \/ (HasCycle /\ ~AllDone /\ ReadyNodes = {} /\ RunningNodes = {})
    \/ AllDone

\* ----------------------------------------------------------------
\*  STREAMING-GRAPH modality (ModalityId = 4)
\*
\*  Mirrors StreamGraph.tla: per-record flow; each node runs
\*  continuously, emitting to successors.  Distinguishing native move:
\*  a downstream node is active (Running) while its upstream is ALSO
\*  still active AND the graph has fan (>=2 in- or out-edges on some
\*  node) OR a cycle.  A simple pipeline chain (Linear) has neither
\*  fan nor cycle: every node has exactly 1 in- and 1 out-edge (except
\*  the endpoints), so per-record overlap across GRAPH branches/cycles
\*  can never manifest.  progressed is therefore set only when
\*  StreamFire fires on a fan/cycle topology.
\*
\*  PASS on Tree (fan-out at root; overlap fires), DAG (fan-out + fan-in),
\*        Cycles (cycle circulation; overlap fires).
\*  VIO on Linear: HasFan=FALSE, HasCycle=FALSE → progressed stays FALSE
\*    through completion → conjunct 1 violated.
\*
\*  Cycle handling: in a cyclic stream graph, records circulate.  This is
\*  modelled by the iterative-cycle action, which lets all nodes be Running
\*  simultaneously (each "consumes" from predecessors continuously).
\*  After a bounded number of records, declare complete.
\* ----------------------------------------------------------------
\* A source node (no predecessors) starts streaming.
StreamStart(n) ==
    /\ ModalityId = 4
    /\ ~complete
    /\ nstate[n] = "NotStarted"
    /\ Preds(n) = {}
    /\ nstate'    = [nstate EXCEPT ![n] = "Running"]
    /\ progressed' = progressed   \* source start alone is not the distinguishing move
    /\ complete'   = complete

\* Per-record fire on a non-source node: node n starts Running while
\* upstream is Running (overlap).  This is the distinguishing move when
\* the graph has fan or cycle topology.
StreamFire(n) ==
    /\ ModalityId = 4
    /\ ~complete
    /\ nstate[n] = "NotStarted"
    /\ \E p \in Preds(n) : nstate[p] = "Running"
    /\ nstate'    = [nstate EXCEPT ![n] = "Running"]
    /\ progressed' = IF (HasFan \/ HasCycle)
                     THEN TRUE
                     ELSE progressed
    /\ complete'   = complete

\* A node completes after it has been Running long enough.
StreamNodeDone(n) ==
    /\ ModalityId = 4
    /\ ~complete
    /\ nstate[n] = "Running"
    /\ \* A node can complete when it has no more work to propagate:
       \* either it has no successors (sink), or all its successors are
       \* already Running or Done (all downstream started).
       \A s \in Succs(n) : nstate[s] # "NotStarted"
    /\ nstate'    = [nstate EXCEPT ![n] = "Done"]
    /\ progressed' = progressed
    /\ complete'   = IF AllDone' THEN TRUE ELSE complete

\* Cycle-stream action: in a cyclic graph, start all nodes simultaneously
\* (continuous circulation).  Fires when HasCycle and no source exists
\* (cycle has no natural start) and no node is yet Running.
StreamCycleStart ==
    /\ ModalityId = 4
    /\ ~complete
    /\ HasCycle
    /\ \A n \in G_Nodes : Preds(n) # {}   \* truly cyclic: no source
    /\ \A n \in G_Nodes : nstate[n] = "NotStarted"
    /\ nstate'    = [n \in G_Nodes |-> "Running"]
    /\ progressed' = TRUE   \* cycle circulation IS the distinguishing stream move
    /\ complete'   = complete

\* Cycle-stream complete: after all cycle nodes have been Running, mark Done.
StreamCycleDone ==
    /\ ModalityId = 4
    /\ ~complete
    /\ HasCycle
    /\ \A n \in G_Nodes : nstate[n] = "Running"
    /\ nstate'    = [n \in G_Nodes |-> "Done"]
    /\ progressed' = progressed
    /\ complete'   = TRUE

StreamCanProgress ==
    \/ \E n \in G_Nodes : nstate[n] = "NotStarted" /\
                          (Preds(n) = {} \/ \E p \in Preds(n) : nstate[p] = "Running")
    \/ \E n \in G_Nodes : nstate[n] = "Running" /\
                          \A s \in Succs(n) : nstate[s] # "NotStarted"
    \/ (HasCycle /\ \A n \in G_Nodes : Preds(n) # {} /\ nstate[n] = "NotStarted")
    \/ (HasCycle /\ \A n \in G_Nodes : nstate[n] = "Running")
    \/ AllDone

\* ----------------------------------------------------------------
\*  Unified CanNativeProgress (dispatches to the active modality)
\* ----------------------------------------------------------------
CanNativeProgress ==
    IF ModalityId = 1 THEN SeqCanProgress
    ELSE IF ModalityId = 2 THEN FJCanProgress
    ELSE IF ModalityId = 3 THEN StepCanProgress
    ELSE StreamCanProgress

\* ----------------------------------------------------------------
\*  Init / Next
\* ----------------------------------------------------------------
Init ==
    /\ nstate     = [n \in G_Nodes |-> "NotStarted"]
    /\ progressed = FALSE
    /\ complete   = FALSE
    /\ checkPhase = "boot"

\* Harness boundary: expose the unchanged native initial state to Admits only
\* after one explicit transition, so deadlock falsifiers carry execution
\* evidence. This is not a modality primitive and changes no runtime state.
BeginAdmissionCheck ==
    /\ checkPhase = "boot"
    /\ checkPhase' = "active"
    /\ UNCHANGED <<nstate, progressed, complete>>

SeqActions    == SeqStep
FJActions     == FJFire
StepActions   == StepBecomeReady \/ StepComplete \/ StepIterativeRound
StreamActions ==
    \/ \E n \in G_Nodes : StreamStart(n)
    \/ \E n \in G_Nodes : StreamFire(n)
    \/ \E n \in G_Nodes : StreamNodeDone(n)
    \/ StreamCycleStart
    \/ StreamCycleDone

ModalityActions ==
    IF ModalityId = 1 THEN SeqActions
    ELSE IF ModalityId = 2 THEN FJActions
    ELSE IF ModalityId = 3 THEN StepActions
    ELSE StreamActions

DoneStuttering == checkPhase = "active" /\ complete /\ UNCHANGED vars

Next ==
    \/ BeginAdmissionCheck
    \/ /\ checkPhase = "active"
       /\ ModalityActions
       /\ UNCHANGED checkPhase
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------
\*  TypeInvariant (always PASS — structural; checked by all 16 cfgs)
\* ----------------------------------------------------------------

\* ----------------------------------------------------------------
\*  Admits  — the single cross-axis admission invariant
\*
\*  Conjunct 1: complete => progressed
\*    PASS cells:  execution always reaches complete with progressed=TRUE.
\*    VIO Type B:  Linear/FJ, Linear/Step, Linear/Stream complete without
\*                 the distinguishing native move ever firing.
\*  Conjunct 2: complete \/ CanNativeProgress
\*    PASS cells:  in every reachable state, either already done or still
\*                 able to make native progress.
\*    VIO Type A:  Cycles/Seq, Cycles/FJ are stuck after the admission-check
\*                 boundary (no source node in the cycle; no ready node; no
\*                 iteration action) without completing.
\* ----------------------------------------------------------------
Admits ==
    \/ checkPhase = "boot"
    \/ /\ checkPhase = "active"
       /\ (complete => progressed)
       /\ (complete \/ CanNativeProgress)

====
