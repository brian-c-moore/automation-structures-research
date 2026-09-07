---- MODULE TCBRequiredDependencyShrink_NEG ----
EXTENDS ALKConstructionTheoremWitness

RequiredBefore == {"kernel-code", "audit-store"}
AddedRequired == {"future-adapter"}
ShrunkenCandidateTCB == RequiredBefore

TCBGrowthAdjacentBoundaryHeld ==
    /\ FixedClaimTCBMonotonicity(
           Dependencies, RequiredBefore, AddedRequired)
    /\ ShrunkenCandidateTCB
         \in SufficientTCBs(Dependencies, RequiredBefore)

TCBRequiredDependencyShrinkHeld ==
    \/ /\ TCBGrowthAdjacentBoundaryHeld
          /\ ShrunkenCandidateTCB
               \in SufficientTCBs(
                      Dependencies, RequiredBefore \cup AddedRequired)
    \/ ExactTCBRequirementGrowthBinding(
           Claims, Dependencies,
           ClaimObligations, ObligationPropertyClass,
           LivenessFairnessOwner,
           GuaranteeClaimant, ALKAuthority,
           AdmittedActions, ClaimCommitActions,
           OwnerOf, DelegateOf, AssuranceProviderOf,
           ActorDependency, EvidenceForCommit,
           EvidenceProducer, CustodianOf, RetentionProviderOf,
           ProviderDependency,
           {"kernel-code"}, AddedRequired)

NegativeControlExpected == NegativeControlGate(TCBRequiredDependencyShrinkHeld)

====
