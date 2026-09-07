---- MODULE CompositionKernel_Proof ----
EXTENDS CompositionKernel, TLAPS

CONSTANTS CompositionStateDomain, CompositionInitialStates,
          CompositionInvA, CompositionInvB,
          CompositionStepA, CompositionStepB, CompositionSharedSteps,
          CompositionEnvironmentSteps, CompositionFailureSteps,
          CompositionInterferenceSteps,
          CompositionRelyA, CompositionRelyB, CompositionRelyEdges,
          CompositionProviders, CompositionUnavailableProviders

THEOREM AcyclicCompositionSafety ==
    /\ CompositionBoundaryPremises(
           CompositionStateDomain, CompositionInitialStates,
           CompositionInvA, CompositionInvB,
           CompositionStepA, CompositionStepB, CompositionSharedSteps,
           CompositionEnvironmentSteps, CompositionFailureSteps,
           CompositionInterferenceSteps,
           CompositionRelyA, CompositionRelyB,
           CompositionProviders, CompositionUnavailableProviders)
    /\ AcyclicSafetyClosure(
           CompositionStateDomain, CompositionInitialStates,
           CompositionInvA, CompositionInvB,
           CompositionStepA, CompositionStepB, CompositionSharedSteps,
           CompositionEnvironmentSteps, CompositionFailureSteps,
           CompositionRelyA, CompositionRelyB, CompositionRelyEdges)
    => CompositionSafetyConclusion(
           CompositionStateDomain, CompositionInitialStates,
           CompositionInvA, CompositionInvB,
           CompositionStepA, CompositionStepB, CompositionSharedSteps,
           CompositionEnvironmentSteps, CompositionFailureSteps,
           CompositionInterferenceSteps)
BY SMT DEF CompositionBoundaryPremises, AcyclicSafetyClosure,
           CrossSafetyUnderAcyclicRelies,
           CommonTransitionsPreserveJoint,
           CompositionSafetyConclusion, ComposedSteps,
           JointInvariant, AcyclicRelyGraph,
           RelyGuaranteeTyped, FailureModelTyped,
           RelationTyped, Pairs, Initializes, Stable

THEOREM MutualClosureCompositionSafety ==
    /\ CompositionBoundaryPremises(
           CompositionStateDomain, CompositionInitialStates,
           CompositionInvA, CompositionInvB,
           CompositionStepA, CompositionStepB, CompositionSharedSteps,
           CompositionEnvironmentSteps, CompositionFailureSteps,
           CompositionInterferenceSteps,
           CompositionRelyA, CompositionRelyB,
           CompositionProviders, CompositionUnavailableProviders)
    /\ MutualSafetyDischarge(
           CompositionStateDomain, CompositionInitialStates,
           CompositionInvA, CompositionInvB,
           CompositionStepA, CompositionStepB, CompositionSharedSteps,
           CompositionEnvironmentSteps, CompositionFailureSteps,
           CompositionRelyA, CompositionRelyB, CompositionRelyEdges)
    => CompositionSafetyConclusion(
           CompositionStateDomain, CompositionInitialStates,
           CompositionInvA, CompositionInvB,
           CompositionStepA, CompositionStepB, CompositionSharedSteps,
           CompositionEnvironmentSteps, CompositionFailureSteps,
           CompositionInterferenceSteps)
BY SMT DEF CompositionBoundaryPremises, MutualSafetyDischarge,
           MutualSafetyClosure, CompositionSafetyConclusion,
           ComposedSteps, JointInvariant, PeerReliesDischarged,
           CyclicRelyGraph, RelyGuaranteeTyped, FailureModelTyped,
           RelationTyped, Pairs, Initializes, Stable

THEOREM CompositionSafety ==
    CompositionSafetyPremises(
        CompositionStateDomain, CompositionInitialStates,
        CompositionInvA, CompositionInvB,
        CompositionStepA, CompositionStepB, CompositionSharedSteps,
        CompositionEnvironmentSteps, CompositionFailureSteps,
        CompositionInterferenceSteps,
        CompositionRelyA, CompositionRelyB, CompositionRelyEdges,
        CompositionProviders, CompositionUnavailableProviders)
    => CompositionSafetyConclusion(
           CompositionStateDomain, CompositionInitialStates,
           CompositionInvA, CompositionInvB,
           CompositionStepA, CompositionStepB, CompositionSharedSteps,
           CompositionEnvironmentSteps, CompositionFailureSteps,
           CompositionInterferenceSteps)
BY AcyclicCompositionSafety, MutualClosureCompositionSafety
   DEF CompositionSafetyPremises

====
