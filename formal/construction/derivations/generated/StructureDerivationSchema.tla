---- MODULE StructureDerivationSchema ----
EXTENDS ConstructionKernel

ConformanceConditions ==
    {"initialization", "step-simulation", "observation-agreement",
     "commit-agreement", "failure-persistence-agreement",
     "rely-discharge", "liveness-preservation", "tcb-closure"}

ExecutionCarriers == {"Sequential", "ForkJoin", "StepGraph", "StreamGraph"}

RefinementStatuses == {"mechanized"}

RangeOf(F) == {F[x] : x \in DOMAIN F}

ActionMapTyped(FormalActions, ExecutableActions, ActionMap) ==
    /\ DOMAIN ActionMap = FormalActions
    /\ \A action \in FormalActions :
          /\ ActionMap[action] \subseteq ExecutableActions
          /\ ActionMap[action] # {}
    /\ UNION {ActionMap[action] : action \in FormalActions}
         = ExecutableActions

StateObservationMapTyped(
        StateFields, ObservationFields, ImplementationStateFields,
        ImplementationStateMap, ObservationMap) ==
    /\ StateFields # {}
    /\ ObservationFields # {}
    /\ ImplementationStateFields # {}
    /\ DOMAIN ImplementationStateMap = ImplementationStateFields
    /\ RangeOf(ImplementationStateMap) = StateFields
    /\ DOMAIN ObservationMap = ObservationFields
    /\ RangeOf(ObservationMap) \subseteq StateFields

ObligationMapTyped(Obligations, Violations, ViolationOf) ==
    /\ Obligations # {}
    /\ Violations # {}
    /\ DOMAIN ViolationOf = Obligations
    /\ RangeOf(ViolationOf) = Violations

PremiseOwnershipTyped(LibraryPremises, DeploymentPremises) ==
    /\ LibraryPremises # {}
    /\ DeploymentPremises # {}
    /\ LibraryPremises \cap DeploymentPremises = {}

ContractCasesTyped(ValidCases, BoundaryCases, MisuseCases, FailureCases) ==
    /\ ValidCases # {}
    /\ BoundaryCases # {}
    /\ MisuseCases # {}
    /\ FailureCases # {}
    /\ ValidCases \cap BoundaryCases = {}
    /\ ValidCases \cap MisuseCases = {}
    /\ ValidCases \cap FailureCases = {}
    /\ BoundaryCases \cap MisuseCases = {}
    /\ BoundaryCases \cap FailureCases = {}
    /\ MisuseCases \cap FailureCases = {}

KernelFamilyRegistrationTyped(
        PropertyClassesUsed, ApplicableFamilies, DischargedFamilies,
        TransferClasses, RefinementStatus) ==
    /\ PropertyClassesUsed # {}
    /\ PropertyClassesUsed \subseteq KernelTracePropertyClasses
    /\ RequiredConstructionFamilies \subseteq ApplicableFamilies
    /\ ApplicableFamilies \subseteq KernelFamilies
    /\ DischargedFamilies \subseteq ApplicableFamilies
    /\ ApplicableFamilies = DischargedFamilies
    /\ TransferClasses # {}
    /\ TransferClasses \subseteq RefinementClasses
    /\ "safety" \in TransferClasses
    /\ ("liveness" \in PropertyClassesUsed
          => /\ "progress" \in ApplicableFamilies
             /\ "liveness" \in TransferClasses)
    /\ ("evidence" \in PropertyClassesUsed
          => "observation" \in TransferClasses)
    /\ RefinementStatus \in RefinementStatuses
    /\ RefinementStatus = "mechanized"

DerivationRecordTyped(r) ==
    /\ r.kind \in {"abstraction-primitive", "named-composition",
                    "execution-modality"}
    /\ r.canonicalActions = r.systemActions \cup r.environmentActions
    /\ r.systemActions \cap r.environmentActions = {}
    /\ r.systemActions # {}
    /\ r.failureActions \subseteq r.environmentActions
    /\ r.commitActions \subseteq r.systemActions
    /\ r.commitActions # {}
    /\ ActionMapTyped(
           r.canonicalActions, r.executableActions, r.actionMap)
    /\ StateObservationMapTyped(
           r.stateFields, r.observationFields,
           r.implementationStateFields,
           r.implementationStateMap, r.observationMap)
    /\ ObligationMapTyped(r.obligations, r.violations, r.violationOf)
    /\ r.claimant \in r.actors
    /\ OwnershipBoundaryTyped(
           r.canonicalActions, r.actors, r.ownerOf, r.delegateOf,
           r.commitActions, r.assuranceAt)
    /\ r.relies # {}
    /\ r.guarantees # {}
    /\ r.runtimeProviders # {}
    /\ r.failureCeilings # {}
    /\ r.executionCarriers # {}
    /\ r.executionCarriers \subseteq ExecutionCarriers
    /\ r.localTheorems # {}
    /\ r.executablePointers # {}
    /\ PremiseOwnershipTyped(r.libraryPremises, r.deploymentPremises)
    /\ r.residuals # {}
    /\ r.evidenceCeilings # {}
    /\ ContractCasesTyped(
           r.validCases, r.boundaryCases,
           r.misuseCases, r.failureCases)
    /\ r.globalAssumptions = GlobalModelingAssumptionNames
    /\ r.conformanceConditions = ConformanceConditions
    /\ KernelFamilyRegistrationTyped(
           r.propertyClasses, r.applicableFamilies,
           r.dischargedFamilies, r.transferClasses,
           r.refinementStatus)

KernelWitnessTyped(r) ==
    /\ r.witnessStates # {}
    /\ r.witnessInitial # {}
    /\ r.witnessViolationStates # {}
    /\ r.witnessObligationStates =
         r.witnessStates \ r.witnessViolationStates
    /\ ActionFamilyTyped(
           r.witnessStates, r.canonicalActions,
           r.witnessActionSteps)
    /\ r.witnessSystemSteps =
         UNION {r.witnessActionSteps[action] :
                  action \in r.systemActions}
    /\ r.witnessEnvironmentSteps =
         UNION {r.witnessActionSteps[action] :
                  action \in r.environmentActions}
    /\ r.witnessCommitSteps =
         UNION {r.witnessActionSteps[action] :
                  action \in r.commitActions}
    /\ r.witnessFailureSteps =
         UNION {r.witnessActionSteps[action] :
                  action \in r.failureActions}
    /\ ObligationPreservationPremises(
           r.witnessStates, r.witnessInitial,
           r.witnessObligationStates,
           r.witnessSystemSteps, r.witnessEnvironmentSteps,
           r.witnessRelySteps)
    /\ r.witnessCommitSteps # {}
    /\ AssuranceBoundaryTyped(
           r.witnessStates, r.witnessActors, r.witnessProviders,
           r.witnessClaimant, r.witnessCommitOwner,
           r.witnessCommitDelegate, r.witnessAssuranceProvider,
           r.witnessAssurancePosition, r.witnessPreventionControllers,
           r.witnessFailureSteps, r.witnessUnavailableProviders,
           r.witnessPersistentObserve, r.witnessPersistentEvidence,
           r.witnessRecoveryAvailable)
    /\ OwnershipAssuranceCeiling(
           r.witnessClaimant, r.witnessCommitOwner,
           r.witnessAssuranceProvider, r.witnessAssurancePosition,
           r.witnessPreventionControllers,
           r.witnessUnavailableProviders,
           r.witnessPersistentEvidence, r.witnessRecoveryAvailable)
    /\ ("check-act" \in r.applicableFamilies
          => CheckActAdmission(
                 r.witnessStates, r.witnessCheckActMode,
                 r.witnessCheckResultStates, r.witnessPredicateStates,
                 r.witnessInterferenceSteps, r.witnessCommitSteps))
    /\ ("progress" \in r.applicableFamilies
          => RankedProgressPremises(
                 r.witnessStates, r.witnessActiveStates,
                 r.witnessClosedStates, r.witnessProgressSteps,
                 r.witnessOtherSteps, r.witnessRankBound, r.witnessRank,
                 r.witnessFairnessOwners, r.witnessFairnessOwner,
                 r.witnessFairnessOwnerOf))
    /\ ExecutionProfileTyped(
           r.witnessStates, r.witnessActiveStates,
           r.witnessClosedStates, r.witnessProgressSteps,
           r.witnessHandoffSteps, r.witnessFailureSteps,
           r.witnessPersistentObserve)

DerivationRecordAccepted(r) ==
    DerivationRecordTyped(r) /\ KernelWitnessTyped(r)

====
