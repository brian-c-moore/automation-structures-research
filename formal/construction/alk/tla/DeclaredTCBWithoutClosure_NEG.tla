---- MODULE DeclaredTCBWithoutClosure_NEG ----
EXTENDS ALKConstructionTheoremWitness

TCBOnlyKernel == [claim \in Claims |-> {"kernel-code"}]
AllActorsUseKernel == [actor \in Actors |-> "kernel-code"]

EvidenceDependencyOmissionHeld ==
    ExactClaimTCBClosure(
        Claims, Obligations, ActionLabels, Actors, Providers,
        EvidenceEvents, Dependencies, TCBOnlyKernel,
        ClaimObligations, ObligationPropertyClass,
        LivenessFairnessOwner,
        GuaranteeClaimant, ALKAuthority,
        AdmittedActions, ClaimCommitActions,
        OwnerOf, DelegateOf, AssuranceProviderOf,
        AllActorsUseKernel, EvidenceForCommit,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        ProviderDependency)

AssuranceDependencies == Dependencies \cup {"assurance-service"}
AssuranceProviderDependency ==
    [provider \in Providers |->
        IF provider = "assurer"
          THEN "assurance-service"
          ELSE ProviderDependency[provider]]
TCBWithoutAssurance == [claim \in Claims |-> Dependencies]

AssuranceDependencyOmissionHeld ==
    ExactClaimTCBClosure(
        Claims, Obligations, ActionLabels, Actors, Providers,
        EvidenceEvents, AssuranceDependencies, TCBWithoutAssurance,
        ClaimObligations, ObligationPropertyClass,
        LivenessFairnessOwner,
        GuaranteeClaimant, ALKAuthority,
        AdmittedActions, ClaimCommitActions,
        OwnerOf, DelegateOf, AssuranceProviderOf,
        ActorDependency, EvidenceForCommit,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        AssuranceProviderDependency)

TemporalObligation == "PropagationPass!EventualSettledOrIterationLimit"
FairnessActors == Actors \cup {"scheduler"}
FairnessDependencies == Dependencies \cup {"scheduler-service"}
FairnessActorDependency ==
    [actor \in FairnessActors |->
        IF actor = "scheduler"
          THEN "scheduler-service"
          ELSE ActorDependency[actor]]
TemporalClaimObligations ==
    [claim \in Claims |-> {TemporalObligation}]
TemporalFairnessOwner ==
    [obligation \in Obligations |->
        IF obligation = TemporalObligation
          THEN "scheduler"
          ELSE LivenessFairnessOwner[obligation]]
TemporalFairnessOwnerOf ==
    [obligation \in Obligations |->
        IF obligation = TemporalObligation
          THEN [action \in ActionLabels |-> "scheduler"]
          ELSE LivenessFairnessOwnerOf[obligation]]
TCBWithoutFairness == [claim \in Claims |-> Dependencies]

TemporalLivenessBoundaryHeld ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, PotentialActions,
        Claims, Obligations, FairnessActors,
        ObligationPropertyClass,
        TemporalClaimObligations, ObligationStates, ViolationStates,
        AllowedRelationSteps, ViolatingActions, DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        LivenessWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        TemporalFairnessOwner, TemporalFairnessOwnerOf)

FairnessDependencyOmissionHeld ==
    ExactClaimTCBClosure(
        Claims, Obligations, ActionLabels, FairnessActors, Providers,
        EvidenceEvents, FairnessDependencies, TCBWithoutFairness,
        TemporalClaimObligations, ObligationPropertyClass,
        TemporalFairnessOwner,
        GuaranteeClaimant, ALKAuthority,
        AdmittedActions, ClaimCommitActions,
        OwnerOf, DelegateOf, AssuranceProviderOf,
        FairnessActorDependency, EvidenceForCommit,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        ProviderDependency)

CollapsedDependencies == Dependencies \cup Actors
CollapsedActorDependency == [actor \in Actors |-> actor]
CollapsedClaimTCB == [claim \in Claims |-> CollapsedDependencies]

AuthorityTCBTypeCollapseHeld ==
    ExactClaimTCBClosure(
        Claims, Obligations, ActionLabels, Actors, Providers,
        EvidenceEvents, CollapsedDependencies, CollapsedClaimTCB,
        ClaimObligations, ObligationPropertyClass,
        LivenessFairnessOwner,
        GuaranteeClaimant, ALKAuthority,
        AdmittedActions, ClaimCommitActions,
        OwnerOf, DelegateOf, AssuranceProviderOf,
        CollapsedActorDependency, EvidenceForCommit,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        ProviderDependency)

ClaimTCBClosureHeld ==
    EvidenceDependencyOmissionHeld
      \/ AssuranceDependencyOmissionHeld
      \/ FairnessDependencyOmissionHeld
      \/ AuthorityTCBTypeCollapseHeld

NegativeControlExpected == NegativeControlGate(ClaimTCBClosureHeld)

====
