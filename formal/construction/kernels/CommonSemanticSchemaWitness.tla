---- MODULE CommonSemanticSchemaWitness ----
EXTENDS CommonSemanticSchema

States == {"open", "closed", "bad"}
InitialStates == {"open"}
ActionLabels == {"commit", "environment"}
AdmittedLabels == {"commit"}
EnvironmentLabels == {"environment"}
CommitSteps == {<<"open", "closed">>}
EnvironmentSteps == IdentityRelation(States)
Actions ==
    [label \in ActionLabels |->
        IF label = "commit" THEN CommitSteps ELSE EnvironmentSteps]

ObservationDomain == {"open-view", "closed-view", "bad-view"}
Observe ==
    [state \in States |->
        CASE state = "open" -> "open-view"
          [] state = "closed" -> "closed-view"
          [] OTHER -> "bad-view"]

Actors == {"builder", "assurer"}
Providers == {"assurer"}
OwnerOf == [label \in ActionLabels |-> "builder"]
DelegateOf == [label \in ActionLabels |-> {"builder"}]
CommitActions == {"commit"}
AssuranceAt == [label \in CommitActions |-> "at-commit"]

ObligationStates == {"open", "closed"}
FailureSteps == {<<"bad", "bad">>}
PersistentObserve == [state \in States |-> state = "closed"]

ClosedStates == {"closed"}
Rank ==
    [state \in States |-> IF state = "closed" THEN 0 ELSE 1]
ProgressSteps == CommitSteps

EvidenceEvents == {"close-event"}
EvidenceSubjects == {"sample-work"}
EvidenceActions == {"commit-action"}
CommitIds == {"commit-id"}
EvidenceClasses == {"evidence"}
EventObservation == [event \in EvidenceEvents |-> "closed-view"]
EventSubject == [event \in EvidenceEvents |-> "sample-work"]
EventAction == [event \in EvidenceEvents |-> "commit-action"]
EventClaimant == [event \in EvidenceEvents |-> "builder"]
EventOwner == [event \in EvidenceEvents |-> "builder"]
EventCommit == [event \in EvidenceEvents |-> "commit-id"]
EventAssurance == [event \in EvidenceEvents |-> "at-commit"]
EventEvidenceClass == [event \in EvidenceEvents |-> "evidence"]

StepA == CommitSteps
StepB == EnvironmentSteps
RelyA == StepB
RelyB == StepA

ImplementationStates == {"i-open", "i-closed", "i-bad"}
ImplementationInitial == {"i-open"}
ImplementationSteps == {<<"i-open", "i-closed">>}
ImplementationCommitSteps == ImplementationSteps
ImplementationFailureSteps == {}
ImplementationProgressSteps == ImplementationSteps
FormalSteps == CommitSteps
FormalFailureSteps == {}
FormalProgressSteps == CommitSteps
Abstraction ==
    [state \in ImplementationStates |->
        CASE state = "i-open" -> "open"
          [] state = "i-closed" -> "closed"
          [] OTHER -> "bad"]
ImplementationObserve ==
    [state \in ImplementationStates |-> Observe[Abstraction[state]]]
ImplementationCommitOwner ==
    [step \in ImplementationCommitSteps |-> "builder"]
FormalCommitOwner == [step \in CommitSteps |-> "builder"]
ImplementationCommitDelegate ==
    [step \in ImplementationCommitSteps |-> "builder"]
FormalCommitDelegate == [step \in CommitSteps |-> "builder"]
ImplementationCommitAssurance ==
    [step \in ImplementationCommitSteps |-> "at-commit"]
FormalCommitAssurance == [step \in CommitSteps |-> "at-commit"]
ImplementationPersistentObserve ==
    [state \in ImplementationStates |->
        PersistentObserve[Abstraction[state]]]

RetainedStructures == {"structure", "execution"}
SelectedStructures == RetainedStructures
Instances == {"structure-instance", "execution-instance"}
StructureOf ==
    [instance \in Instances |->
        IF instance = "structure-instance" THEN "structure" ELSE "execution"]
ParameterDomain == {"domain"}
ParameterDomainOf ==
    [structure \in SelectedStructures |-> ParameterDomain]
Parameters == [instance \in Instances |-> "domain"]

SystemTransitionHeld ==
    SystemTransition(States, AdmittedLabels, EnvironmentLabels, Actions)

ObligationTypingHeld ==
    ObligationTyped(
        States, ObligationStates, States \ ObligationStates,
        Actors, "builder")

OwnershipBoundaryHeld ==
    OwnershipBoundaryTyped(
        ActionLabels, Actors, OwnerOf, DelegateOf,
        CommitActions, AssuranceAt)

RelyGuaranteeHeld ==
    RelyGuaranteeTyped(States, EnvironmentSteps, CommitSteps)

FailureModelHeld ==
    FailureModelTyped(States, FailureSteps, {}, Providers)

GuaranteeRegistrationHeld ==
    GuaranteeRegistrationTyped(
        "prevention", "safety", ObservationDomain, Observe)

ExecutionProfileHeld ==
    ExecutionProfileTyped(
        States, States \ ClosedStates, ClosedStates,
        ProgressSteps, {}, FailureSteps, PersistentObserve)

EvidenceProfileHeld ==
    EvidenceProfileTyped(
        EvidenceEvents, ObservationDomain, EvidenceSubjects,
        EvidenceActions, Actors, CommitIds, EvidenceClasses,
        EventObservation, EventSubject, EventAction,
        EventClaimant, EventOwner, EventCommit,
        EventAssurance, EventEvidenceClass)

CompositionBoundaryHeld ==
    CompositionBoundaryTyped(
        States, StepA \cup StepB, {}, EnvironmentSteps, StepA)

MutualCompositionHeld ==
    AdmittedMutualComposition(
        States, InitialStates, States,
        StepA, StepB, {}, {}, RelyA, RelyB)

ImplementationConformanceHeld ==
    CheckableImplementationConformance(
        ImplementationStates, States,
        ImplementationInitial, InitialStates,
        ImplementationSteps, FormalSteps,
        ImplementationCommitSteps, CommitSteps,
        ImplementationFailureSteps, FormalFailureSteps,
        ImplementationProgressSteps, FormalProgressSteps,
        {}, {}, ImplementationSteps, ObservationDomain,
        ImplementationCommitOwner, FormalCommitOwner,
        ImplementationCommitDelegate, FormalCommitDelegate,
        ImplementationCommitAssurance, FormalCommitAssurance,
        ImplementationPersistentObserve, PersistentObserve,
        Abstraction, ImplementationObserve, Observe)

BuilderSelectionHeld ==
    BuilderSelection(RetainedStructures, SelectedStructures)

BuilderInstantiationHeld ==
    BuilderInstantiation(
        SelectedStructures, Instances, StructureOf,
        ParameterDomain, ParameterDomainOf, Parameters)

PremiseBoundaryHeld ==
    PremiseBoundary(
        {"library-premise"}, {"deployment-premise"},
        {"library-premise", "deployment-premise"})

\* A fixed domain keeps violating evaluations visible during omission tests.
ClauseDomain == {"good", "left-only", "right-only", "bad"}
ClauseNames == {"left", "right", "support", "derived", "policy"}
ClauseRoleOf ==
    [clause \in ClauseNames |->
        CASE clause \in {"left", "right"} -> "contributing"
          [] clause = "support" -> "support"
          [] clause = "derived" -> "derived-conditional"
          [] OTHER -> "selected-policy"]
ClauseMeaning ==
    [clause \in ClauseNames |->
        CASE clause = "left" -> {"good", "left-only"}
          [] clause = "right" -> {"good", "right-only"}
          [] clause = "support" -> {"good", "left-only"}
          [] clause = "derived" -> {"good"}
          [] OTHER -> {"good", "left-only", "right-only"}]
ResponsibilityMeaning == {"good"}
ClauseProofDomain == {"good", "left-only"}
ClauseDerivedBasis == [clause \in {"derived"} |-> {"left"}]
ClausePremiseDomain ==
    [clause \in {"derived"} |-> {"good", "right-only"}]

ClauseBindingHeld ==
    SemanticClauseBinding(
        "state-safety", ClauseDomain, ClauseNames, ClauseRoleOf,
        ClauseMeaning, ResponsibilityMeaning, ClauseProofDomain,
        ClauseDerivedBasis, ClausePremiseDomain)

\* Each rejected input changes one seam; the domain and responsibility stay fixed.
OmittedContributingClauseRejected ==
    ~SemanticClauseBinding(
        "state-safety", ClauseDomain, ClauseNames, ClauseRoleOf,
        [ClauseMeaning EXCEPT !["right"] = ClauseDomain],
        ResponsibilityMeaning, ClauseProofDomain,
        ClauseDerivedBasis, ClausePremiseDomain)

UnsupportedProofDomainRejected ==
    ~SemanticClauseBinding(
        "state-safety", ClauseDomain, ClauseNames, ClauseRoleOf,
        [ClauseMeaning EXCEPT !["support"] = {"left-only"}],
        ResponsibilityMeaning, ClauseProofDomain,
        ClauseDerivedBasis, ClausePremiseDomain)

MissingDerivationPremiseRejected ==
    ~SemanticClauseBinding(
        "state-safety", ClauseDomain, ClauseNames, ClauseRoleOf,
        ClauseMeaning, ResponsibilityMeaning, ClauseProofDomain,
        ClauseDerivedBasis, [clause \in {"derived"} |-> ClauseDomain])

VARIABLE witness

vars == <<witness>>

Init == witness = 0

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

====
