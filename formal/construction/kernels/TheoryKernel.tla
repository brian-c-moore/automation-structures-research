---- MODULE TheoryKernel ----
EXTENDS CommonSemanticSchema

PermittedSteps(SystemSteps, EnvironmentSteps) ==
    SystemSteps \cup EnvironmentSteps

ObligationPreservationPremises(
        S, InitialStates, ObligationStates,
        SystemSteps, EnvironmentSteps, RelySteps) ==
    /\ InitialStates \subseteq S
    /\ ObligationStates \subseteq S
    /\ RelationTyped(S, SystemSteps)
    /\ RelationTyped(S, EnvironmentSteps)
    /\ RelationTyped(S, RelySteps)
    /\ Initializes(InitialStates, ObligationStates)
    /\ Stable(S, ObligationStates, SystemSteps)
    /\ EnvironmentSteps \subseteq RelySteps
    /\ Stable(S, ObligationStates, RelySteps)

ObligationPreservationConclusion(
        S, InitialStates, ObligationStates,
        SystemSteps, EnvironmentSteps) ==
    /\ Initializes(InitialStates, ObligationStates)
    /\ Stable(
           S, ObligationStates,
           PermittedSteps(SystemSteps, EnvironmentSteps))

InvariantSupersets(S, StartStates, Steps) ==
    {PredicateStates \in SUBSET S :
        /\ StartStates \subseteq PredicateStates
        /\ Stable(S, PredicateStates, Steps)}

ReachableUnder(S, StartStates, Steps) ==
    {s \in S :
        \A PredicateStates \in InvariantSupersets(S, StartStates, Steps) :
            s \in PredicateStates}

StepSourceStates(S, Steps) ==
    {s \in S : \E t \in S : <<s, t>> \in Steps}

StableCheckActPremises(
        S, CheckResultStates, PredicateStates,
        InterferenceSteps, GovernedCommitSteps) ==
    /\ CheckResultStates \subseteq S
    /\ PredicateStates \subseteq S
    /\ RelationTyped(S, InterferenceSteps)
    /\ RelationTyped(S, GovernedCommitSteps)
    /\ GovernedCommitSteps # {}
    /\ CheckResultStates \subseteq PredicateStates
    /\ Stable(S, PredicateStates, InterferenceSteps)
    /\ StepSourceStates(S, GovernedCommitSteps)
         \subseteq ReachableUnder(S, CheckResultStates, InterferenceSteps)

AtomicCheckActPremises(
        S, CheckResultStates, PredicateStates,
        GovernedCommitSteps) ==
    /\ CheckResultStates \subseteq S
    /\ PredicateStates \subseteq S
    /\ RelationTyped(S, GovernedCommitSteps)
    /\ GovernedCommitSteps # {}
    /\ CheckResultStates \subseteq PredicateStates
    /\ StepSourceStates(S, GovernedCommitSteps)
         \subseteq CheckResultStates

CheckActModes == {"stable", "atomic"}

CheckActAdmission(
        S, CheckActMode, CheckResultStates, PredicateStates,
        InterferenceSteps, GovernedCommitSteps) ==
    /\ CheckActMode \in CheckActModes
    /\ IF CheckActMode = "stable"
          THEN StableCheckActPremises(
                   S, CheckResultStates, PredicateStates,
                   InterferenceSteps, GovernedCommitSteps)
          ELSE AtomicCheckActPremises(
                   S, CheckResultStates, PredicateStates,
                   GovernedCommitSteps)

CheckActLicensed(S, PredicateStates, GovernedCommitSteps) ==
    StepSourceStates(S, GovernedCommitSteps) \subseteq PredicateStates

====
