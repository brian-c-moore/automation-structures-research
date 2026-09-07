---- MODULE BudgetDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"capacity", "allocated", "reserved", "pending_eviction"} |->
        CASE key = "capacity" -> "capacity"
          [] key = "allocated" -> "allocated"
          [] key = "reserved" -> "reserved"
          [] key = "pending_eviction" -> "pending_eviction"
          [] OTHER -> "pending_eviction"]

ObservationMap ==
    [key \in {"capacity", "allocated", "reserved", "pending_eviction"} |->
        CASE key = "capacity" -> "capacity"
          [] key = "allocated" -> "allocated"
          [] key = "reserved" -> "reserved"
          [] key = "pending_eviction" -> "pending_eviction"
          [] OTHER -> "pending_eviction"]

ActionMap ==
    [key \in {"TryAllocate", "Reserve", "CommitReservation", "Release", "MarkEviction", "CompleteEviction"} |->
        CASE key = "TryAllocate" -> {"try_allocate"}
          [] key = "Reserve" -> {"reserve"}
          [] key = "CommitReservation" -> {"commit_reservation"}
          [] key = "Release" -> {"release"}
          [] key = "MarkEviction" -> {"mark_eviction"}
          [] key = "CompleteEviction" -> {"complete_eviction"}
          [] OTHER -> {"complete_eviction"}]

ViolationOf ==
    [key \in {"SafetyInvariant"} |->
        CASE key = "SafetyInvariant" -> "CapacityExceeded"
          [] OTHER -> "CapacityExceeded"]

OwnerOf ==
    [key \in {"TryAllocate", "Reserve", "CommitReservation", "Release", "MarkEviction", "CompleteEviction"} |->
        CASE key = "TryAllocate" -> "budget-authority"
          [] key = "Reserve" -> "budget-authority"
          [] key = "CommitReservation" -> "budget-authority"
          [] key = "Release" -> "budget-authority"
          [] key = "MarkEviction" -> "budget-authority"
          [] key = "CompleteEviction" -> "budget-authority"
          [] OTHER -> "budget-authority"]

DelegateOf ==
    [key \in {"TryAllocate", "Reserve", "CommitReservation", "Release", "MarkEviction", "CompleteEviction"} |->
        CASE key = "TryAllocate" -> {"budget-authority"}
          [] key = "Reserve" -> {"budget-authority"}
          [] key = "CommitReservation" -> {"budget-authority"}
          [] key = "Release" -> {"budget-authority"}
          [] key = "MarkEviction" -> {"budget-authority"}
          [] key = "CompleteEviction" -> {"budget-authority"}
          [] OTHER -> {"budget-authority"}]

AssuranceAt ==
    [key \in {"TryAllocate", "Reserve", "CommitReservation", "Release", "MarkEviction", "CompleteEviction"} |->
        CASE key = "TryAllocate" -> "at-commit"
          [] key = "Reserve" -> "at-commit"
          [] key = "CommitReservation" -> "at-commit"
          [] key = "Release" -> "at-commit"
          [] key = "MarkEviction" -> "at-commit"
          [] key = "CompleteEviction" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"empty", "safe-used", "safe-reserved", "safe-evicting", "overspent"} |->
        CASE key = "empty" -> TRUE
          [] key = "safe-used" -> TRUE
          [] key = "safe-reserved" -> TRUE
          [] key = "safe-evicting" -> TRUE
          [] key = "overspent" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"empty", "safe-used", "safe-reserved", "safe-evicting", "overspent"} |->
        CASE key = "empty" -> 0
          [] key = "safe-used" -> 0
          [] key = "safe-reserved" -> 0
          [] key = "safe-evicting" -> 0
          [] key = "overspent" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"TryAllocate", "Reserve", "CommitReservation", "Release", "MarkEviction", "CompleteEviction"} |->
        CASE key = "TryAllocate" -> {<<"empty", "safe-used">>}
          [] key = "Reserve" -> {<<"empty", "safe-reserved">>}
          [] key = "CommitReservation" -> {<<"safe-reserved", "safe-used">>}
          [] key = "Release" -> {<<"safe-used", "empty">>}
          [] key = "MarkEviction" -> {<<"safe-used", "safe-evicting">>}
          [] key = "CompleteEviction" -> {<<"safe-evicting", "empty">>}
          [] OTHER -> {<<"safe-evicting", "empty">>}]

Derivation ==
    [structure |-> "Budget",
     kind |-> "abstraction-primitive",
     propertyClasses |-> {"safety"},
     stateFields |-> {"capacity", "allocated", "reserved", "pending_eviction"},
     observationFields |-> {"capacity", "allocated", "reserved", "pending_eviction"},
     implementationStateFields |-> {"capacity", "allocated", "reserved", "pending_eviction"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"TryAllocate", "Reserve", "CommitReservation", "Release", "MarkEviction", "CompleteEviction"},
     systemActions |-> {"TryAllocate", "Reserve", "CommitReservation", "Release", "MarkEviction", "CompleteEviction"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"TryAllocate", "Reserve", "CommitReservation", "Release", "MarkEviction", "CompleteEviction"},
     executableActions |-> {"try_allocate", "reserve", "commit_reservation", "release", "mark_eviction", "complete_eviction"},
     actionMap |-> ActionMap,
     obligations |-> {"SafetyInvariant"},
     violations |-> {"CapacityExceeded"},
     violationOf |-> ViolationOf,
     actors |-> {"budget-claimant", "budget-authority"},
     claimant |-> "budget-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"serialized-exclusive-ledger-mutation", "atomic-guard-and-update", "complete-ledger-tcb-with-no-bypass"},
     guarantees |-> {"capacity-preservation", "guarded-commit-license", "budget-owner-ceiling", "budget-executable-transfer"},
     runtimeProviders |-> {"budget-authority", "exclusive-mutation-provider", "integer-representation"},
     failureCeilings |-> {"no-modeled-crash-or-torn-write", "weak-memory-and-nonlinearizable-ledgers-outside-boundary", "u64-call-domain-requires-the-declared-refinement-boundary"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"Budget_Proof!SafetyInvariantSafety", "BudgetImplRefinesSpec_Proof!RefinementThm", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"crate://automation-structures/0.2.3/src/primitives/budget.rs", "formal/structures/Budget/refinement/BudgetImplRefinesSpec.tla", "formal/structures/Budget/refinement/BudgetImplRefinesSpec_Proof.tla"},
     libraryPremises |-> {"canonical-six-action-ledger", "SafetyInvariantSafety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification", "Budget-contract-refinement"},
     deploymentPremises |-> {"CapacityType", "serialized-exclusive-ledger-mutation", "atomic-guard-and-update", "u64-arithmetic-agrees-with-Nat-inside-the-invariant", "complete-ledger-tcb-with-no-bypass"},
     residuals |-> {"no-distributed-or-concurrent-ledger-protocol", "no-durability-or-recovery-result", "zero-and-over-capacity-executable-calls-refine-stutter-only-under-the-written-Budget-mapping"},
     evidenceCeilings |-> {"TLAPS-proves-unbounded-Nat-safety-under-CapacityType", "Verus-proves-the-written-u64-contracts", "the-existing-Budget-refinement-is-component-evidence-not-the-bounded-sufficiency-six-record-bridge"},
     validCases |-> {"allocate-within-headroom", "reservation-lifecycle"},
     boundaryCases |-> {"exact-capacity", "rejected-overspend-stutter"},
     misuseCases |-> {"split-check-and-commit", "omitted-ledger-term"},
     failureCases |-> {"torn-ledger-update", "bypass-writer"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"empty", "safe-used", "safe-reserved", "safe-evicting", "overspent"},
     witnessInitial |-> {"empty"},
     witnessObligationStates |-> {"empty", "safe-used", "safe-reserved", "safe-evicting"},
     witnessViolationStates |-> {"overspent"},
     witnessSystemSteps |-> {<<"empty", "safe-used">>, <<"empty", "safe-reserved">>, <<"safe-reserved", "safe-used">>, <<"safe-used", "empty">>, <<"safe-used", "safe-evicting">>, <<"safe-evicting", "empty">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"empty", "safe-used">>, <<"empty", "safe-reserved">>, <<"safe-reserved", "safe-used">>, <<"safe-used", "empty">>, <<"safe-used", "safe-evicting">>, <<"safe-evicting", "empty">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"empty", "safe-used", "safe-reserved", "safe-evicting"},
     witnessPredicateStates |-> {"empty", "safe-used", "safe-reserved", "safe-evicting"},
     witnessActors |-> {"budget-claimant", "budget-authority"},
     witnessProviders |-> {"budget-authority"},
     witnessClaimant |-> "budget-claimant",
     witnessCommitOwner |-> "budget-authority",
     witnessCommitDelegate |-> "budget-authority",
     witnessAssuranceProvider |-> "budget-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"budget-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"empty", "safe-used", "safe-reserved", "safe-evicting"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"budget-authority"},
     witnessFairnessOwner |-> "budget-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
