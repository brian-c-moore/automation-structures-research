---- MODULE CiCdCarrierBinding ----
\* Safety model for the nested carrier premises used by FEX-DOM-CICD-01,
\* FEX-DOM-CICD-03, and FEX-ASM-06.
\*
\* The model follows the accepted StepGraph and ForkJoin donor roles. It checks
\* exact dependency binding, predecessor-governed release, complete worker
\* coverage, barrier-before-output order, outer-to-inner completion, debit
\* identity, and target-effect identity for one finite successful workflow.

EXTENDS Naturals, FiniteSets

CONSTANTS Compile, Static, Test, Package, Linux, Windows, NULL, Fault

Jobs == {Compile, Static, Test, Package}
Workers == {Linux, Windows}
ChargedWork == {Compile, Static, Linux, Windows, Package}
Lifecycle == {"waiting", "running", "done"}
JoinPhases == {"fork", "join", "published"}

Faults == {
    "None",
    "EarlyExecution",
    "MissingPredecessor",
    "SkipJoin",
    "DropWorkerCompletion",
    "FlattenSequential",
    "BypassDebit",
    "MisdirectEffect",
    "CompleteTestEarly"
}

ASSUME ModelTypes ==
    /\ Compile # Static
    /\ Compile # Test
    /\ Compile # Package
    /\ Static # Test
    /\ Static # Package
    /\ Test # Package
    /\ Linux # Windows
    /\ NULL \notin ChargedWork
    /\ Fault \in Faults

DeclaredPredecessors(job) ==
    CASE job = Compile -> {}
      [] job = Static -> {Compile}
      [] job = Test -> {Compile}
      [] job = Package -> {Static, Test}

CarrierPredecessors(job) ==
    IF Fault = "MissingPredecessor" /\ job = Package
    THEN {Static}
    ELSE DeclaredPredecessors(job)

DeclaredCharge(work) == IF work = Compile THEN 2 ELSE 1

VARIABLES
    jobState, workerState, joinPhase, barrierCrossed,
    completedWork, debits, targets, dependencyBound, outerCarrier, innerCarrier

vars == <<
    jobState, workerState, joinPhase, barrierCrossed,
    completedWork, debits, targets, dependencyBound, outerCarrier, innerCarrier
>>

TypeInvariant ==
    /\ jobState \in [Jobs -> Lifecycle]
    /\ workerState \in [Workers -> Lifecycle]
    /\ joinPhase \in JoinPhases
    /\ barrierCrossed \in BOOLEAN
    /\ completedWork \subseteq ChargedWork
    /\ debits \in [ChargedWork -> Nat]
    /\ targets \in [ChargedWork -> ChargedWork \cup {NULL}]
    /\ dependencyBound \in BOOLEAN
    /\ outerCarrier \in BOOLEAN
    /\ innerCarrier \in BOOLEAN

DependencyBinding ==
    /\ dependencyBound
    /\ \A job \in Jobs : CarrierPredecessors(job) = DeclaredPredecessors(job)

DependencyRelease ==
    \A job \in Jobs :
        jobState[job] \in {"running", "done"} =>
            \A predecessor \in DeclaredPredecessors(job) :
                jobState[predecessor] = "done"

PartitionCoverage ==
    joinPhase \in {"join", "published"} =>
        \A worker \in Workers : workerState[worker] = "done"

BarrierOrder == joinPhase = "published" => barrierCrossed

NestedHandoff ==
    jobState[Test] = "done" =>
        /\ joinPhase = "published"
        /\ barrierCrossed
        /\ \A worker \in Workers : workerState[worker] = "done"

DebitIdentity ==
    \A work \in completedWork : debits[work] = DeclaredCharge(work)

EffectBinding == \A work \in completedWork : targets[work] = work

CarrierPresence == outerCarrier /\ innerCarrier

CompositionInvariant ==
    /\ DependencyBinding
    /\ DependencyRelease
    /\ PartitionCoverage
    /\ BarrierOrder
    /\ NestedHandoff
    /\ DebitIdentity
    /\ EffectBinding
    /\ CarrierPresence

Init ==
    /\ jobState = [job \in Jobs |-> "waiting"]
    /\ workerState = [worker \in Workers |-> "waiting"]
    /\ joinPhase = "fork"
    /\ barrierCrossed = FALSE
    /\ completedWork = {}
    /\ debits = [work \in ChargedWork |-> 0]
    /\ targets = [work \in ChargedWork |-> NULL]
    /\ dependencyBound = (Fault # "MissingPredecessor")
    /\ outerCarrier = (Fault # "FlattenSequential")
    /\ innerCarrier = (Fault # "FlattenSequential")

StartJob(job) ==
    /\ job \in Jobs
    /\ jobState[job] = "waiting"
    /\ \/ \A predecessor \in CarrierPredecessors(job) :
              jobState[predecessor] = "done"
       \/ /\ Fault = "EarlyExecution"
          /\ job = Package
          /\ jobState[Compile] = "done"
    /\ jobState' = [jobState EXCEPT ![job] = "running"]
    /\ UNCHANGED <<
        workerState, joinPhase, barrierCrossed,
        completedWork, debits, targets, dependencyBound, outerCarrier, innerCarrier
        >>

CompleteJob(job) ==
    /\ job \in {Compile, Static, Package}
    /\ jobState[job] = "running"
    /\ jobState' = [jobState EXCEPT ![job] = "done"]
    /\ completedWork' = completedWork \cup {job}
    /\ debits' = [debits EXCEPT
        ![job] = IF Fault = "BypassDebit" /\ job = Package
                 THEN 0
                 ELSE DeclaredCharge(job)]
    /\ targets' = [targets EXCEPT
        ![job] = IF Fault = "MisdirectEffect" /\ job = Static
                  THEN Package
                  ELSE job]
    /\ UNCHANGED <<
        workerState, joinPhase, barrierCrossed, dependencyBound, outerCarrier, innerCarrier
        >>

StartWorker(worker) ==
    /\ worker \in Workers
    /\ jobState[Test] = "running"
    /\ joinPhase = "fork"
    /\ workerState[worker] = "waiting"
    /\ workerState' = [workerState EXCEPT ![worker] = "running"]
    /\ UNCHANGED <<
        jobState, joinPhase, barrierCrossed,
        completedWork, debits, targets, dependencyBound, outerCarrier, innerCarrier
        >>

CompleteWorker(worker) ==
    /\ worker \in Workers
    /\ workerState[worker] = "running"
    /\ workerState' = [workerState EXCEPT ![worker] = "done"]
    /\ completedWork' = completedWork \cup {worker}
    /\ debits' = [debits EXCEPT ![worker] = DeclaredCharge(worker)]
    /\ targets' = [targets EXCEPT ![worker] = worker]
    /\ UNCHANGED <<
        jobState, joinPhase, barrierCrossed, dependencyBound, outerCarrier, innerCarrier
        >>

CrossBarrier ==
    /\ joinPhase = "fork"
    /\ \/ \A worker \in Workers : workerState[worker] = "done"
       \/ Fault = "DropWorkerCompletion"
    /\ joinPhase' = "join"
    /\ barrierCrossed' = TRUE
    /\ UNCHANGED <<
        jobState, workerState, completedWork, debits, targets,
        dependencyBound, outerCarrier, innerCarrier
        >>

PublishOutput ==
    /\ \/ joinPhase = "join"
       \/ /\ Fault = "SkipJoin"
          /\ joinPhase = "fork"
    /\ joinPhase' = "published"
    /\ UNCHANGED <<
        jobState, workerState, barrierCrossed,
        completedWork, debits, targets, dependencyBound, outerCarrier, innerCarrier
        >>

CompleteTest ==
    /\ jobState[Test] = "running"
    /\ \/ joinPhase = "published"
       \/ /\ Fault = "CompleteTestEarly"
          /\ joinPhase = "fork"
    /\ jobState' = [jobState EXCEPT ![Test] = "done"]
    /\ UNCHANGED <<
        workerState, joinPhase, barrierCrossed,
        completedWork, debits, targets, dependencyBound, outerCarrier, innerCarrier
        >>

Done == \A job \in Jobs : jobState[job] = "done"

Next ==
    \/ \E job \in Jobs : StartJob(job)
    \/ \E job \in {Compile, Static, Package} : CompleteJob(job)
    \/ \E worker \in Workers : StartWorker(worker)
    \/ \E worker \in Workers : CompleteWorker(worker)
    \/ CrossBarrier
    \/ PublishOutput
    \/ CompleteTest
    \/ /\ Done
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

====
