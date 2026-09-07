---- MODULE CrdtPremiseBinding ----
\* Safety model for the state-based composition premises used by
\* FEX-DOM-DIST-01. The cited CRDT results remain the authority for the
\* general convergence implication. This model checks the construction side:
\* identity-content consistency, exact inflationary join, target identity,
\* complete delivery before convergence, and ordered delivery commits.

EXTENDS Naturals, FiniteSets

CONSTANTS
    Replicas, P, Q, Ops, OpA, OpB, Contents, ContentA, ContentB,
    Content(_), MaxDeliveries, NULL, Fault

Faults == {
    "None",
    "IdentityConflict",
    "LeftBiasedMerge",
    "DropRemoteOperation",
    "MisdirectTarget",
    "IncompleteDelivery",
    "SkipActuation"
}

ASSUME ModelTypes ==
    /\ Replicas = {P, Q}
    /\ P # Q
    /\ Ops = {OpA, OpB}
    /\ OpA # OpB
    /\ Contents = {ContentA, ContentB}
    /\ ContentA # ContentB
    /\ \A op \in Ops : Content(op) \in Contents
    /\ MaxDeliveries \in Nat \ {0}
    /\ NULL \notin Replicas \cup Ops \cup Contents
    /\ Fault \in Faults

VARIABLES
    phase, states, identityContents,
    source, target, actualTarget, payload,
    beforeStates, beforeTarget, merged,
    begun, reductions, actuations, completed

vars == <<
    phase, states, identityContents,
    source, target, actualTarget, payload,
    beforeStates, beforeTarget, merged,
    begun, reductions, actuations, completed
>>

ConfiguredContent(op) == IF op = OpA THEN ContentA ELSE ContentB

Join(left, right) ==
    IF Fault = "LeftBiasedMerge" THEN left
    ELSE IF Fault = "DropRemoteOperation" THEN left \cup (right \ {OpB})
    ELSE left \cup right

TypeInvariant ==
    /\ phase \in {"idle", "begun", "reduced", "applied", "done"}
    /\ states \in [Replicas -> SUBSET Ops]
    /\ identityContents \in [Ops -> SUBSET Contents]
    /\ source \in Replicas \cup {NULL}
    /\ target \in Replicas \cup {NULL}
    /\ actualTarget \in Replicas \cup {NULL}
    /\ payload \subseteq Ops
    /\ beforeStates \in [Replicas -> SUBSET Ops]
    /\ beforeTarget \subseteq Ops
    /\ merged \subseteq Ops
    /\ begun \in 0..MaxDeliveries
    /\ reductions \in 0..MaxDeliveries
    /\ actuations \in 0..MaxDeliveries
    /\ completed \in 0..MaxDeliveries

IdentityContentConsistency ==
    \A op \in Ops : Cardinality(identityContents[op]) = 1

ExactJoinFunction ==
    \A left, right \in SUBSET Ops : Join(left, right) = left \cup right

ExactJoinBinding == reductions > 0 => ExactJoinFunction

JoinLaws ==
    /\ \A left, right \in SUBSET Ops :
        /\ left \subseteq Join(left, right)
        /\ right \subseteq Join(left, right)
        /\ Join(left, left) = left
        /\ Join(left, right) = Join(right, left)
    /\ \A left, right, third \in SUBSET Ops :
        Join(Join(left, right), third) = Join(left, Join(right, third))

JoinLawBinding == reductions > 0 => JoinLaws

ReductionBinding ==
    phase \in {"reduced", "applied"} =>
        /\ merged = Join(beforeTarget, payload)
        /\ beforeTarget \subseteq merged
        /\ payload \subseteq merged

TargetBinding ==
    phase = "applied" =>
        /\ actualTarget = target
        /\ states[target] = merged
        /\ \A replica \in Replicas \ {target} : states[replica] = beforeStates[replica]

CompleteDelivery ==
    phase = "done" => \A replica \in Replicas : states[replica] = Ops

StrongConvergence ==
    phase = "done" => states[P] = states[Q]

SequentialOrder ==
    /\ completed <= actuations
    /\ actuations <= reductions
    /\ reductions <= begun
    /\ begun <= completed + 1

CompositionInvariant ==
    /\ IdentityContentConsistency
    /\ ExactJoinBinding
    /\ JoinLawBinding
    /\ ReductionBinding
    /\ TargetBinding
    /\ CompleteDelivery
    /\ StrongConvergence
    /\ SequentialOrder

Init ==
    /\ phase = "idle"
    /\ states = [replica \in Replicas |-> IF replica = P THEN {OpA} ELSE {OpB}]
    /\ identityContents = [op \in Ops |-> {Content(op)}]
    /\ source = NULL
    /\ target = NULL
    /\ actualTarget = NULL
    /\ payload = {}
    /\ beforeStates = states
    /\ beforeTarget = {}
    /\ merged = {}
    /\ begun = 0
    /\ reductions = 0
    /\ actuations = 0
    /\ completed = 0

CorruptIdentity ==
    /\ Fault = "IdentityConflict"
    /\ phase = "idle"
    /\ identityContents' = [identityContents EXCEPT ![OpA] = @ \cup {ContentB}]
    /\ UNCHANGED <<
        phase, states, source, target, actualTarget, payload,
        beforeStates, beforeTarget, merged,
        begun, reductions, actuations, completed
        >>

BeginDelivery(from, to) ==
    /\ phase = "idle"
    /\ begun < MaxDeliveries
    /\ from \in Replicas
    /\ to \in Replicas \ {from}
    /\ source' = from
    /\ target' = to
    /\ actualTarget' = NULL
    /\ payload' = states[from]
    /\ beforeStates' = states
    /\ beforeTarget' = states[to]
    /\ merged' = {}
    /\ begun' = begun + 1
    /\ phase' = "begun"
    /\ UNCHANGED <<
        states, identityContents, reductions, actuations, completed
        >>

Reduce ==
    /\ phase = "begun"
    /\ merged' = Join(beforeTarget, payload)
    /\ reductions' = reductions + 1
    /\ phase' = "reduced"
    /\ UNCHANGED <<
        states, identityContents, source, target, actualTarget,
        payload, beforeStates, beforeTarget,
        begun, actuations, completed
        >>

Actuate ==
    /\ phase = "reduced"
    /\ actualTarget' =
        IF Fault = "MisdirectTarget"
        THEN CHOOSE replica \in Replicas : replica # target
        ELSE target
    /\ states' = [states EXCEPT ![actualTarget'] = merged]
    /\ actuations' = actuations + 1
    /\ phase' = "applied"
    /\ UNCHANGED <<
        identityContents, source, target, payload,
        beforeStates, beforeTarget, merged,
        begun, reductions, completed
        >>

CompleteStep ==
    /\ \/ phase = "applied"
       \/ /\ Fault = "SkipActuation"
          /\ phase = "reduced"
    /\ completed' = completed + 1
    /\ phase' = "idle"
    /\ UNCHANGED <<
        states, identityContents, source, target, actualTarget,
        payload, beforeStates, beforeTarget, merged,
        begun, reductions, actuations
        >>

Finish ==
    /\ phase = "idle"
    /\ \/ \A replica \in Replicas : states[replica] = Ops
       \/ Fault = "IncompleteDelivery"
    /\ phase' = "done"
    /\ UNCHANGED <<
        states, identityContents, source, target, actualTarget,
        payload, beforeStates, beforeTarget, merged,
        begun, reductions, actuations, completed
        >>

Next ==
    \/ CorruptIdentity
    \/ \E from, to \in Replicas : BeginDelivery(from, to)
    \/ Reduce
    \/ Actuate
    \/ CompleteStep
    \/ Finish

Spec == Init /\ [][Next]_vars

====
