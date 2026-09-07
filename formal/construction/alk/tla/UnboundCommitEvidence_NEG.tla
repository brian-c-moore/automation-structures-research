---- MODULE UnboundCommitEvidence_NEG ----
EXTENDS ALKConstructionTheoremWitness

UnboundEvidenceForCommit == [action \in {"commit"} |-> {}]

UnboundCommitEvidenceHeld ==
    OwnedCommitEvidencePremises(
        States, KernelCheckActMode,
        KernelCheckResultStates, KernelPredicateStates,
        KernelInterferenceSteps, GovernedCommitSteps,
        Claims, Subjects, ActionLabels, Actors, Providers,
        EvidenceEvents, ClaimCommitActions, EvidenceRequiredActions,
        UnboundEvidenceForCommit,
        ClaimSubject, GuaranteeClaimant, OwnerOf,
        AssurancePositionOf,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance,
        EvidenceProducer, CustodianOf, RetentionProviderOf)

OmittedEvidenceRequiredActions == [claim \in Claims |-> {}]

OmittedEvidenceRequirementHeld ==
    ExactEvidenceRequirementBinding(
        Claims, ActionLabels,
        RegisteredGuarantees, GuaranteeKindOf,
        GuaranteePropertyClass,
        ClaimCommitActions, OmittedEvidenceRequiredActions)

MisattributedEventOwner ==
    [event \in EvidenceEvents |-> "custodian"]

MisattributedCommitEvidenceHeld ==
    OwnedCommitEvidencePremises(
        States, KernelCheckActMode,
        KernelCheckResultStates, KernelPredicateStates,
        KernelInterferenceSteps, GovernedCommitSteps,
        Claims, Subjects, ActionLabels, Actors, Providers,
        EvidenceEvents, ClaimCommitActions, EvidenceRequiredActions,
        EvidenceForCommit,
        ClaimSubject, GuaranteeClaimant, OwnerOf,
        AssurancePositionOf,
        EventSubject, EventAction, EventClaimant,
        MisattributedEventOwner, EventCommit, EventAssurance,
        EvidenceProducer, CustodianOf, RetentionProviderOf)

AliasedEvidenceEvents == {"commit-event", "alias-event"}
AliasedEvidenceForCommit ==
    [action \in {"commit"} |-> AliasedEvidenceEvents]
AliasedEventObservation ==
    [event \in AliasedEvidenceEvents |-> "closed-view"]
AliasedEventSubject ==
    [event \in AliasedEvidenceEvents |-> "work"]
AliasedEventAction ==
    [event \in AliasedEvidenceEvents |-> "commit"]
AliasedEventClaimant ==
    [event \in AliasedEvidenceEvents |-> "builder"]
AliasedEventOwner ==
    [event \in AliasedEvidenceEvents |-> "builder"]
AliasedEventCommit ==
    [event \in AliasedEvidenceEvents |-> "commit"]
AliasedEventAssurance ==
    [event \in AliasedEvidenceEvents |-> "at-commit"]
AliasedEventEvidenceClass ==
    [event \in AliasedEvidenceEvents |-> "evidence"]
AliasedEvidenceProducer ==
    [event \in AliasedEvidenceEvents |-> "builder"]
AliasedCustodianOf ==
    [event \in AliasedEvidenceEvents |-> "custodian"]
AliasedRetentionProviderOf ==
    [event \in AliasedEvidenceEvents |-> "audit-provider"]
AliasedEvidenceKernelEvent ==
    [event \in AliasedEvidenceEvents |-> "kernel-commit-event"]

AliasedCommitEvidenceBoundaryHeld ==
    ExactCommitEvidencePremises(
        Claims, Subjects, ActionLabels, Actors, Providers,
        AliasedEvidenceEvents, ClaimCommitActions,
        EvidenceRequiredActions, AliasedEvidenceForCommit,
        ClaimSubject, GuaranteeClaimant, OwnerOf,
        AssurancePositionOf,
        AliasedEventSubject, AliasedEventAction,
        AliasedEventClaimant, AliasedEventOwner,
        AliasedEventCommit, AliasedEventAssurance,
        AliasedEvidenceProducer, AliasedCustodianOf,
        AliasedRetentionProviderOf)

AliasedKernelEvidenceBindingHeld ==
    KernelEvidenceBinding(
        Claims, AliasedEvidenceEvents, KernelEvidenceEvents,
        EvidenceRequiredActions, AliasedEvidenceForCommit,
        FormalCommitSteps,
        AliasedEvidenceKernelEvent,
        AliasedEventObservation,
        AliasedEventSubject, AliasedEventAction,
        AliasedEventClaimant, AliasedEventOwner,
        AliasedEventCommit, AliasedEventAssurance,
        AliasedEventEvidenceClass,
        PostMediationSteps,
        KernelEventObservation,
        KernelEventSubject, KernelEventAction,
        KernelEventClaimant, KernelEventOwner,
        KernelEventCommit, KernelEventAssurance,
        KernelEventEvidenceClass)

ExpandedPostMediationSteps ==
    [action \in ActionLabels |->
        IF action = "commit"
          THEN PostMediationSteps[action] \cup {<<"open", "open">>}
          ELSE PostMediationSteps[action]]
MismatchedKernelEventAction ==
    [event \in KernelEvidenceEvents |-> <<"open", "open">>]

KernelCommitActionMismatchHeld ==
    KernelEvidenceBinding(
        Claims, EvidenceEvents, KernelEvidenceEvents,
        EvidenceRequiredActions, EvidenceForCommit,
        FormalCommitSteps,
        EvidenceKernelEvent,
        EventObservation,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance, EventEvidenceClass,
        ExpandedPostMediationSteps,
        KernelEventObservation,
        KernelEventSubject, MismatchedKernelEventAction,
        KernelEventClaimant, KernelEventOwner,
        KernelEventCommit, KernelEventAssurance,
        KernelEventEvidenceClass)

MismatchedEventObservation ==
    [event \in EvidenceEvents |-> "open-view"]
KernelObservationMismatchHeld ==
    KernelEvidenceBinding(
        Claims, EvidenceEvents, KernelEvidenceEvents,
        EvidenceRequiredActions, EvidenceForCommit,
        FormalCommitSteps,
        EvidenceKernelEvent,
        MismatchedEventObservation,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance, EventEvidenceClass,
        PostMediationSteps,
        KernelEventObservation,
        KernelEventSubject, KernelEventAction,
        KernelEventClaimant, KernelEventOwner,
        KernelEventCommit, KernelEventAssurance,
        KernelEventEvidenceClass)

MismatchedEventEvidenceClass ==
    [event \in EvidenceEvents |-> "safety"]
KernelEvidenceClassMismatchHeld ==
    KernelEvidenceBinding(
        Claims, EvidenceEvents, KernelEvidenceEvents,
        EvidenceRequiredActions, EvidenceForCommit,
        FormalCommitSteps,
        EvidenceKernelEvent,
        EventObservation,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance, MismatchedEventEvidenceClass,
        PostMediationSteps,
        KernelEventObservation,
        KernelEventSubject, KernelEventAction,
        KernelEventClaimant, KernelEventOwner,
        KernelEventCommit, KernelEventAssurance,
        KernelEventEvidenceClass)

ExpandedFormalCommitSteps ==
    FormalCommitSteps \cup {<<"closed", "closed">>}
ExpandedCommitPotentialActions ==
    [action \in ActionLabels |->
        IF action = "commit"
          THEN PotentialActions[action] \cup {<<"closed", "closed">>}
          ELSE PotentialActions[action]]
ExpandedCommitPostMediationSteps ==
    [action \in ActionLabels |->
        IF action = "commit"
          THEN PostMediationSteps[action] \cup {<<"closed", "closed">>}
          ELSE PostMediationSteps[action]]
ExpandedFormalCommitOwner ==
    [step \in ExpandedFormalCommitSteps |-> "builder"]
ExpandedFormalCommitDelegate ==
    [step \in ExpandedFormalCommitSteps |-> "builder"]
ExpandedFormalCommitAssurance ==
    [step \in ExpandedFormalCommitSteps |-> "at-commit"]

ExpandedKernelCommitAssuranceHeld ==
    KernelCommitAssuranceBinding(
        Claims, ActionLabels, ExpandedCommitPotentialActions,
        ExpandedCommitPostMediationSteps,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf, DelegateOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor,
        ExpandedFormalCommitSteps, ExpandedFormalCommitOwner,
        ExpandedFormalCommitDelegate,
        ExpandedFormalCommitAssurance,
        KernelClaimant, KernelAssuranceProvider,
        KernelPreventionControllers, KernelUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)

IncompleteKernelCommitEvidenceCoverageHeld ==
    KernelEvidenceBinding(
        Claims, EvidenceEvents, KernelEvidenceEvents,
        EvidenceRequiredActions, EvidenceForCommit,
        ExpandedFormalCommitSteps,
        EvidenceKernelEvent,
        EventObservation,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance, EventEvidenceClass,
        ExpandedCommitPostMediationSteps,
        KernelEventObservation,
        KernelEventSubject, KernelEventAction,
        KernelEventClaimant, KernelEventOwner,
        KernelEventCommit, KernelEventAssurance,
        KernelEventEvidenceClass)

CommitEvidenceBindingHeld ==
    UnboundCommitEvidenceHeld
      \/ OmittedEvidenceRequirementHeld
      \/ MisattributedCommitEvidenceHeld
      \/ AliasedKernelEvidenceBindingHeld
      \/ KernelCommitActionMismatchHeld
      \/ KernelObservationMismatchHeld
      \/ KernelEvidenceClassMismatchHeld
      \/ IncompleteKernelCommitEvidenceCoverageHeld

NegativeControlExpected == NegativeControlGate(CommitEvidenceBindingHeld)

====
