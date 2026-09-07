---- MODULE BisectionDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"lo", "hi", "probes_taken"} |->
        CASE key = "lo" -> "lo"
          [] key = "hi" -> "hi"
          [] key = "probes_taken" -> "probes_taken"
          [] OTHER -> "probes_taken"]

ObservationMap ==
    [key \in {"lo", "hi", "probes_taken"} |->
        CASE key = "lo" -> "lo"
          [] key = "hi" -> "hi"
          [] key = "probes_taken" -> "probes_taken"
          [] OTHER -> "probes_taken"]

ActionMap ==
    [key \in {"ProbeLeft", "ProbeRight", "Converged"} |->
        CASE key = "ProbeLeft" -> {"probe"}
          [] key = "ProbeRight" -> {"probe"}
          [] key = "Converged" -> {"converged"}
          [] OTHER -> {"converged"}]

ViolationOf ==
    [key \in {"Halving", "MonotonicityPreservation", "ProbeBound", "EventualConvergence"} |->
        CASE key = "Halving" -> "NoncontractingProbe"
          [] key = "MonotonicityPreservation" -> "ThresholdExcluded"
          [] key = "ProbeBound" -> "ProbeBudgetExceeded"
          [] key = "EventualConvergence" -> "InfiniteFairNonconvergence"
          [] OTHER -> "InfiniteFairNonconvergence"]

OwnerOf ==
    [key \in {"ProbeLeft", "ProbeRight", "Converged"} |->
        CASE key = "ProbeLeft" -> "bisection-authority"
          [] key = "ProbeRight" -> "bisection-authority"
          [] key = "Converged" -> "bisection-authority"
          [] OTHER -> "bisection-authority"]

DelegateOf ==
    [key \in {"ProbeLeft", "ProbeRight", "Converged"} |->
        CASE key = "ProbeLeft" -> {"bisection-authority"}
          [] key = "ProbeRight" -> {"bisection-authority"}
          [] key = "Converged" -> {"bisection-authority"}
          [] OTHER -> {"bisection-authority"}]

AssuranceAt ==
    [key \in {"ProbeLeft", "ProbeRight"} |->
        CASE key = "ProbeLeft" -> "at-commit"
          [] key = "ProbeRight" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"wide", "narrow", "converged", "nonconvergent"} |->
        CASE key = "wide" -> TRUE
          [] key = "narrow" -> TRUE
          [] key = "converged" -> TRUE
          [] key = "nonconvergent" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"wide", "narrow", "converged", "nonconvergent"} |->
        CASE key = "wide" -> 2
          [] key = "narrow" -> 1
          [] key = "converged" -> 0
          [] key = "nonconvergent" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf ==
    [key \in {<<"wide", "narrow">>, <<"narrow", "converged">>} |->
        CASE key = <<"wide", "narrow">> -> "probe-scheduler"
          [] key = <<"narrow", "converged">> -> "probe-scheduler"
          [] OTHER -> "probe-scheduler"]

WitnessActionSteps ==
    [key \in {"ProbeLeft", "ProbeRight", "Converged"} |->
        CASE key = "ProbeLeft" -> {<<"wide", "narrow">>, <<"narrow", "converged">>}
          [] key = "ProbeRight" -> {<<"wide", "narrow">>, <<"narrow", "converged">>}
          [] key = "Converged" -> {<<"converged", "converged">>}
          [] OTHER -> {<<"converged", "converged">>}]

Derivation ==
    [structure |-> "Bisection",
     kind |-> "named-composition",
     propertyClasses |-> {"safety", "liveness"},
     stateFields |-> {"lo", "hi", "probes_taken"},
     observationFields |-> {"lo", "hi", "probes_taken"},
     implementationStateFields |-> {"lo", "hi", "probes_taken"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"ProbeLeft", "ProbeRight", "Converged"},
     systemActions |-> {"ProbeLeft", "ProbeRight", "Converged"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"ProbeLeft", "ProbeRight"},
     executableActions |-> {"probe", "converged"},
     actionMap |-> ActionMap,
     obligations |-> {"Halving", "MonotonicityPreservation", "ProbeBound", "EventualConvergence"},
     violations |-> {"NoncontractingProbe", "ThresholdExcluded", "ProbeBudgetExceeded", "InfiniteFairNonconvergence"},
     violationOf |-> ViolationOf,
     actors |-> {"bisection-claimant", "bisection-authority", "probe-scheduler"},
     claimant |-> "bisection-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"ordered-monotone-threshold-domain", "domain-fits-declared-probe-budget", "weak-fair-probe-scheduling", "serialized-interval-mutation"},
     guarantees |-> {"bisection-written-profile-refinement", "bounded-halving-safety", "eventual-bisection-convergence", "atomic-probe-license", "bisection-owner-ceiling"},
     runtimeProviders |-> {"bisection-authority", "probe-scheduler", "ordered-domain-provider"},
     failureCeilings |-> {"no-modeled-crash-or-torn-probe", "predicate-or-domain-change-outside-boundary", "scheduler-fairness-is-deployment-owned"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"BisectionImplRefinesSpec_Proof!RefinementThm", "Bisection_Proof!Safety", "Bisection_Proof!HalvingProperty", "Bisection_Proof!EventualConvergenceProved", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "ProgressKernel_Proof!RankedProgress", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/Bisection/refinement/BisectionImplRefinesSpec.tla", "formal/structures/Bisection/refinement/BisectionImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/compositions/bisection.rs", "formal/structures/Bisection/Bisection.tla", "formal/structures/Bisection/Bisection_Proof.tla"},
     libraryPremises |-> {"Bisection-written-contract-refinement-profile", "canonical-bisection-machine", "Bisection-Safety", "HalvingProperty", "EventualConvergenceProved", "ObligationPreservation", "CheckActStability", "RankedProgress", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"DomainSizeType", "MaxProbesType", "ThresholdType", "DomainFitsProbes", "weak-fair-probe-scheduling", "serialized-interval-mutation"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-time-bound-or-probe-latency-result", "no-concurrent-or-distributed-search", "no-correctness-for-changing-or-nonmonotone-predicates"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-parametric-safety-halving-and-fair-eventual-convergence", "Verus-proves-the-written-u64-bounded-loop-carrier", "liveness-transfers-only-under-the-named-weak-fair-scheduler"},
     validCases |-> {"fair-halving-probes"},
     boundaryCases |-> {"width-below-two"},
     misuseCases |-> {"undersized-probe-budget"},
     failureCases |-> {"torn-probe-update"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "progress", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "progress", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety", "liveness"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"wide", "narrow", "converged", "nonconvergent"},
     witnessInitial |-> {"wide"},
     witnessObligationStates |-> {"wide", "narrow", "converged"},
     witnessViolationStates |-> {"nonconvergent"},
     witnessSystemSteps |-> {<<"wide", "narrow">>, <<"narrow", "converged">>, <<"converged", "converged">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"wide", "narrow">>, <<"narrow", "converged">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"wide", "narrow", "converged"},
     witnessPredicateStates |-> {"wide", "narrow", "converged"},
     witnessActors |-> {"bisection-claimant", "bisection-authority", "probe-scheduler"},
     witnessProviders |-> {"bisection-authority", "probe-scheduler"},
     witnessClaimant |-> "bisection-claimant",
     witnessCommitOwner |-> "bisection-authority",
     witnessCommitDelegate |-> "bisection-authority",
     witnessAssuranceProvider |-> "bisection-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"bisection-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"wide", "narrow"},
     witnessClosedStates |-> {"converged", "nonconvergent"},
     witnessProgressSteps |-> {<<"wide", "narrow">>, <<"narrow", "converged">>},
     witnessOtherSteps |-> {<<"converged", "converged">>, <<"nonconvergent", "nonconvergent">>},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 2,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"probe-scheduler"},
     witnessFairnessOwner |-> "probe-scheduler",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
