---- MODULE TheoryKernel_Proof ----
EXTENDS TheoryKernel, TLAPS

CONSTANTS ObligationStateDomain, ObligationInitialStates,
          RegisteredObligationStates, ObligationSystemSteps,
          ObligationEnvironmentSteps, ObligationRelySteps,
          KernelCheckActMode, KernelCheckResultStates,
          KernelPredicateStates, KernelInterferenceSteps,
          KernelGovernedCommitSteps

THEOREM ObligationPreservation ==
    ObligationPreservationPremises(
        ObligationStateDomain, ObligationInitialStates,
        RegisteredObligationStates, ObligationSystemSteps,
        ObligationEnvironmentSteps, ObligationRelySteps)
    => ObligationPreservationConclusion(
           ObligationStateDomain, ObligationInitialStates,
           RegisteredObligationStates, ObligationSystemSteps,
           ObligationEnvironmentSteps)
BY SMT DEF ObligationPreservationPremises,
           ObligationPreservationConclusion, PermittedSteps,
           Initializes, Stable

LEMMA InterferenceReachabilityPreservesPredicate ==
    /\ KernelCheckResultStates \subseteq ObligationStateDomain
    /\ KernelPredicateStates \subseteq ObligationStateDomain
    /\ RelationTyped(ObligationStateDomain, KernelInterferenceSteps)
    /\ KernelCheckResultStates \subseteq KernelPredicateStates
    /\ Stable(ObligationStateDomain, KernelPredicateStates,
              KernelInterferenceSteps)
    => ReachableUnder(ObligationStateDomain, KernelCheckResultStates,
                      KernelInterferenceSteps)
         \subseteq KernelPredicateStates
BY SMT DEF ReachableUnder, InvariantSupersets

THEOREM CheckActStability ==
    CheckActAdmission(
        ObligationStateDomain, KernelCheckActMode,
        KernelCheckResultStates, KernelPredicateStates,
        KernelInterferenceSteps, KernelGovernedCommitSteps)
    => CheckActLicensed(ObligationStateDomain, KernelPredicateStates,
                        KernelGovernedCommitSteps)
PROOF
  <1> SUFFICES ASSUME
        CheckActAdmission(
            ObligationStateDomain, KernelCheckActMode,
            KernelCheckResultStates, KernelPredicateStates,
            KernelInterferenceSteps, KernelGovernedCommitSteps)
      PROVE CheckActLicensed(
                ObligationStateDomain, KernelPredicateStates,
                KernelGovernedCommitSteps)
    OBVIOUS
  <1>stable. CASE KernelCheckActMode = "stable"
    <2>1. StableCheckActPremises(
             ObligationStateDomain, KernelCheckResultStates,
             KernelPredicateStates, KernelInterferenceSteps,
             KernelGovernedCommitSteps)
      BY <1>stable DEF CheckActAdmission, CheckActModes
    <2>2. ReachableUnder(ObligationStateDomain,
             KernelCheckResultStates, KernelInterferenceSteps)
             \subseteq KernelPredicateStates
      BY <2>1, InterferenceReachabilityPreservesPredicate
         DEF StableCheckActPremises
    <2> QED BY <2>1, <2>2
         DEF StableCheckActPremises, CheckActLicensed
  <1>atomic. CASE KernelCheckActMode = "atomic"
    BY <1>atomic
       DEF CheckActAdmission, CheckActModes,
           AtomicCheckActPremises, CheckActLicensed
  <1> QED BY <1>stable, <1>atomic
       DEF CheckActAdmission, CheckActModes

====
