---- MODULE OwnershipAssuranceKernel ----
EXTENDS TheoryKernel

AssuranceBoundaryTyped(
        S, Actors, Providers,
        Claimant, CommitOwner, CommitDelegate, AssuranceProvider,
        AssurancePosition, PreventionControllers,
        FailureSteps, UnavailableProviders,
        PersistentEvidenceObserve, PersistentEvidence,
        RecoveryAvailable) ==
    /\ Claimant \in Actors
    /\ CommitOwner \in Actors
    /\ CommitDelegate \in Actors
    /\ Providers \subseteq Actors
    /\ AssuranceProvider \in Providers
    /\ AssurancePosition \in AssurancePositions
    /\ PreventionControllers \subseteq Actors
    /\ FailureModelTyped(
           S, FailureSteps, UnavailableProviders, Providers)
    /\ PersistentEvidenceObserve \in [S -> BOOLEAN]
    /\ PersistentEvidence \in BOOLEAN
    /\ PersistentEvidence =
         PersistentAcross(S, PersistentEvidenceObserve, FailureSteps)
    /\ RecoveryAvailable \in BOOLEAN

AssuranceHealthy(AssuranceProvider, UnavailableProviders) ==
    AssuranceProvider \notin UnavailableProviders

\* Claimant receives the claim. CommitOwner owns the governed commit and
\* issues the guarantee. PreventionControllers are inside that owner's
\* fused check-act enforcement path; an out-of-band assurance source is not.
PreventionSupported(
        Claimant, CommitOwner, AssuranceProvider,
        AssurancePosition, PreventionControllers,
        UnavailableProviders) ==
    /\ AssuranceHealthy(AssuranceProvider, UnavailableProviders)
    /\ AssurancePosition \in {"precommit", "at-commit"}
    /\ Claimant = CommitOwner
       \/ AssuranceProvider \in PreventionControllers

DetectionSupported(
        AssuranceProvider, AssurancePosition,
        UnavailableProviders, PersistentEvidence) ==
    /\ AssuranceHealthy(AssuranceProvider, UnavailableProviders)
    /\ AssurancePosition \in {"at-commit", "postcommit"}
    /\ PersistentEvidence

RecoverySupported(
        AssuranceProvider, AssurancePosition,
        UnavailableProviders, PersistentEvidence,
        RecoveryAvailable) ==
    /\ DetectionSupported(
           AssuranceProvider, AssurancePosition,
           UnavailableProviders, PersistentEvidence)
    /\ RecoveryAvailable

\* Read this ceiling from CommitOwner to Claimant. AssuranceProvider can
\* supply a premise, but does not issue the guarantee for CommitOwner.
GuaranteeCeiling(
        Claimant, CommitOwner, AssuranceProvider,
        AssurancePosition, PreventionControllers,
        UnavailableProviders, PersistentEvidence,
        RecoveryAvailable) ==
    {"lost"}
    \cup (IF AssurancePosition # "none" THEN {"conditional"} ELSE {})
    \cup (IF PreventionSupported(
                Claimant, CommitOwner, AssuranceProvider,
                AssurancePosition, PreventionControllers,
                UnavailableProviders)
          THEN {"prevention"} ELSE {})
    \cup (IF DetectionSupported(
                AssuranceProvider, AssurancePosition,
                UnavailableProviders, PersistentEvidence)
          THEN {"detection"} ELSE {})
    \cup (IF RecoverySupported(
                AssuranceProvider, AssurancePosition,
                UnavailableProviders, PersistentEvidence,
                RecoveryAvailable)
          THEN {"recovery"} ELSE {})

OwnershipAssuranceCeiling(
        Claimant, CommitOwner, AssuranceProvider,
        AssurancePosition, PreventionControllers,
        UnavailableProviders, PersistentEvidence,
        RecoveryAvailable) ==
    LET Ceiling ==
          GuaranteeCeiling(
              Claimant, CommitOwner, AssuranceProvider,
              AssurancePosition, PreventionControllers,
              UnavailableProviders, PersistentEvidence,
              RecoveryAvailable)
    IN
    /\ Ceiling \subseteq GuaranteeKinds
    /\ "prevention" \in Ceiling
         => PreventionSupported(
                Claimant, CommitOwner, AssuranceProvider,
                AssurancePosition, PreventionControllers,
                UnavailableProviders)
    /\ "detection" \in Ceiling
         => DetectionSupported(
                AssuranceProvider, AssurancePosition,
                UnavailableProviders, PersistentEvidence)
    /\ "recovery" \in Ceiling
         => RecoverySupported(
                AssuranceProvider, AssurancePosition,
                UnavailableProviders, PersistentEvidence,
                RecoveryAvailable)
    /\ ~AssuranceHealthy(AssuranceProvider, UnavailableProviders)
         => Ceiling \subseteq {"conditional", "lost"}
    /\ AssurancePosition = "postcommit"
         => "prevention" \notin Ceiling
    /\ AssurancePosition = "none"
         => Ceiling = {"lost"}

====
