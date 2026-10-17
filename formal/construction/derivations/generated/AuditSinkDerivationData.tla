---- MODULE AuditSinkDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"log", "last_hash"} |->
        CASE key = "log" -> "log"
          [] key = "last_hash" -> "last_hash"
          [] OTHER -> "last_hash"]

ObservationMap ==
    [key \in {"audit-log", "last-hash", "record-event"} |->
        CASE key = "audit-log" -> "log"
          [] key = "last-hash" -> "last_hash"
          [] key = "record-event" -> "log"
          [] OTHER -> "log"]

ActionMap ==
    [key \in {"Record"} |->
        CASE key = "Record" -> {"record"}
          [] OTHER -> {"record"}]

ViolationOf ==
    [key \in {"ChainIntegrity", "HashConsistency", "HashBindsContent", "TamperEvidentInv"} |->
        CASE key = "ChainIntegrity" -> "BrokenPredecessorLink"
          [] key = "HashConsistency" -> "LastHashMismatch"
          [] key = "HashBindsContent" -> "StoredHashMismatch"
          [] key = "TamperEvidentInv" -> "AmbiguousHashPreimage"
          [] OTHER -> "AmbiguousHashPreimage"]

OwnerOf ==
    [key \in {"Record"} |->
        CASE key = "Record" -> "audit-owner"
          [] OTHER -> "audit-owner"]

DelegateOf ==
    [key \in {"Record"} |->
        CASE key = "Record" -> {"audit-owner"}
          [] OTHER -> {"audit-owner"}]

AssuranceAt ==
    [key \in {"Record"} |->
        CASE key = "Record" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"empty", "recorded", "tampered", "lost"} |->
        CASE key = "empty" -> TRUE
          [] key = "recorded" -> TRUE
          [] key = "tampered" -> FALSE
          [] key = "lost" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"empty", "recorded", "tampered", "lost"} |->
        CASE key = "empty" -> 1
          [] key = "recorded" -> 1
          [] key = "tampered" -> 0
          [] key = "lost" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"Record"} |->
        CASE key = "Record" -> {<<"empty", "recorded">>, <<"recorded", "recorded">>}
          [] OTHER -> {<<"empty", "recorded">>, <<"recorded", "recorded">>}]

Derivation ==
    [structure |-> "AuditSink",
     kind |-> "abstraction-primitive",
     propertyClasses |-> {"safety", "evidence"},
     stateFields |-> {"log", "last_hash"},
     observationFields |-> {"audit-log", "last-hash", "record-event"},
     implementationStateFields |-> {"log", "last_hash"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"Record"},
     systemActions |-> {"Record"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"Record"},
     executableActions |-> {"record"},
     actionMap |-> ActionMap,
     obligations |-> {"ChainIntegrity", "HashConsistency", "HashBindsContent", "TamperEvidentInv"},
     violations |-> {"BrokenPredecessorLink", "LastHashMismatch", "StoredHashMismatch", "AmbiguousHashPreimage"},
     violationOf |-> ViolationOf,
     actors |-> {"audit-claimant", "audit-owner", "audit-storage", "hash-provider"},
     claimant |-> "audit-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"atomic-log-and-last-hash-append", "HashType", "HashCR-for-TamperEvident-only", "persistent-custody-for-cross-failure-evidence", "complete-audit-writer-tcb-with-no-tamper-transition"},
     guarantees |-> {"auditsink-written-profile-refinement", "audit-chain-structure", "conditional-tamper-evidence", "audit-assurance-ceiling", "audit-executable-transfer"},
     runtimeProviders |-> {"audit-owner", "audit-storage", "hash-provider"},
     failureCeilings |-> {"canonical-model-has-no-tamper-crash-or-storage-loss-transition", "persistence-across-process-or-storage-failure-is-deployment-supplied", "HashCR-is-external-and-not-discharged-by-the-modulo-100-executable-hash", "postcommit-observation-does-not-prove-prevention-of-an-external-effect"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"AuditSinkImplRefinesSpec_Proof!RefinementThm", "AuditSink_Proof!SafetyOriginal", "AuditSink_Proof!TamperEvident", "TheoryKernel_Proof!ObligationPreservation", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/AuditSink/refinement/AuditSinkImplRefinesSpec.tla", "formal/structures/AuditSink/refinement/AuditSinkImplRefinesSpec_Proof.tla", "development-copy://automation-structures/0.3.2/src/primitives/audit_sink.rs", "formal/structures/AuditSink/AuditSink.tla", "formal/structures/AuditSink/AuditSink_Proof.tla"},
     libraryPremises |-> {"AuditSink-written-contract-refinement-profile", "canonical-atomic-Record-machine", "SafetyOriginal", "TamperEvident-conditional-theorem", "ObligationPreservation", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"MaxLogLenType", "HashType", "HashCR", "atomic-log-and-last-hash-append", "persistent-custody-for-cross-failure-evidence", "complete-audit-writer-tcb-with-no-tamper-transition"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "the-canonical-state-machine-models-no-adversarial-tamper-action", "the-concrete-modulo-100-hash-intentionally-has-collisions", "durability-freshness-custody-and-external-acceptance-remain-deployment-properties", "no-recovery-result-is-proved"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "SafetyOriginal-is-structural-append-safety", "TamperEvident-is-conditional-on-HashCR", "Verus-validate-is-exact-for-the-concrete-chain-invariant-not-collision-resistance", "record-observation-is-attributable-only-to-the-mapped-Record-commit", "executable-observation-transfer-is-limited-to-the-mapped-record-and-validate-profile"},
     validCases |-> {"atomic-record-append", "conditional-content-attribution"},
     boundaryCases |-> {"empty-genesis", "maximum-log-length"},
     misuseCases |-> {"claim-concrete-collision-resistance", "unlinked-evidence-event"},
     failureCases |-> {"record-loss-after-commit", "hash-provider-violates-HashCR"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety", "observation"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"empty", "recorded", "tampered", "lost"},
     witnessInitial |-> {"empty"},
     witnessObligationStates |-> {"empty", "recorded"},
     witnessViolationStates |-> {"tampered", "lost"},
     witnessSystemSteps |-> {<<"empty", "recorded">>, <<"recorded", "recorded">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"empty", "recorded">>, <<"recorded", "recorded">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {},
     witnessPredicateStates |-> {},
     witnessActors |-> {"audit-claimant", "audit-owner", "audit-storage", "hash-provider"},
     witnessProviders |-> {"audit-owner", "audit-storage", "hash-provider"},
     witnessClaimant |-> "audit-claimant",
     witnessCommitOwner |-> "audit-owner",
     witnessCommitDelegate |-> "audit-owner",
     witnessAssuranceProvider |-> "audit-owner",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"audit-owner"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"empty", "recorded"},
     witnessClosedStates |-> {"tampered", "lost"},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 1,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"audit-owner"},
     witnessFairnessOwner |-> "audit-owner",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
