---- MODULE BoundedSufficiency ----
VARIABLES phase, authorized, committed, evidence

vars == <<phase, authorized, committed, evidence>>

Phases == {"idle", "active", "closed"}

TypeInvariant ==
    /\ phase \in Phases
    /\ authorized \in BOOLEAN
    /\ committed \in BOOLEAN
    /\ evidence \in BOOLEAN

AuthorizationObligation == committed => authorized
EvidenceAttribution == evidence = committed
CommitPhaseAgreement == committed = (phase = "closed")
ActiveAuthorization == phase = "active" => authorized

Inv ==
    /\ TypeInvariant
    /\ AuthorizationObligation
    /\ EvidenceAttribution
    /\ CommitPhaseAgreement
    /\ ActiveAuthorization

Init ==
    /\ phase = "idle"
    /\ authorized = FALSE
    /\ committed = FALSE
    /\ evidence = FALSE

Admit ==
    /\ phase = "idle"
    /\ phase' = "active"
    /\ authorized' = TRUE
    /\ UNCHANGED <<committed, evidence>>

GovernedCommit ==
    /\ phase = "active"
    /\ authorized
    /\ ~committed
    /\ phase' = "closed"
    /\ committed' = TRUE
    /\ evidence' = TRUE
    /\ UNCHANGED authorized

ClosedStuttering ==
    /\ phase = "closed"
    /\ UNCHANGED vars

ProgressStep == Admit \/ GovernedCommit

Next == ProgressStep \/ ClosedStuttering

Fairness == WF_vars(ProgressStep)

Spec == Init /\ [][Next]_vars /\ Fairness
UnfairSpec == Init /\ [][Next]_vars

Closed == phase = "closed"
EventualClosure == <>Closed

ConcreteObservation ==
    [phase |-> phase, closed |-> committed]

AbstractObservation ==
    [phase |-> phase, closed |-> (phase = "closed")]

ObservationAgreement == ConcreteObservation = AbstractObservation

AbstractVars == <<phase>>

AbstractInit == phase = "idle"

AbstractAdmit ==
    /\ phase = "idle"
    /\ phase' = "active"

AbstractCommit ==
    /\ phase = "active"
    /\ phase' = "closed"

AbstractClosedStuttering ==
    /\ phase = "closed"
    /\ UNCHANGED AbstractVars

AbstractNext ==
    AbstractAdmit \/ AbstractCommit \/ AbstractClosedStuttering

AbstractSpec == AbstractInit /\ [][AbstractNext]_AbstractVars

Refinement == AbstractSpec

RegisteredGuaranteeBundle ==
    /\ []AuthorizationObligation
    /\ []EvidenceAttribution
    /\ EventualClosure
    /\ []ObservationAgreement
    /\ Refinement

====
