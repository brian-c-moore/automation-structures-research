---- MODULE ALKClaimProgressWitness ----
EXTENDS ALKClaimAuthorityBinding

\* A distinct claim: the catalog Sequential contract is safety-only.
\* This finite progress specialization adds weak fairness for its actual
\* nonstuttering actions. It does not rename SomeActionEnabled as liveness.
ProgressFrame ==
    [SequentialFrame EXCEPT
        !.obligation = "two-step-sequential-completion",
        !.observationBoundary = "complete-sequential-infinite-behavior",
        !.authorityBoundary = "sequential-writer-and-scheduler",
        !.failureModel = "finite-steps-no-crash-weakly-fair-scheduler",
        !.propertyForm = "liveness"]

ProgressDecisive == SequentialBehaviors \cup {"schedule-sequential"}
ProgressDecisiveOf == [frame \in {ProgressFrame} |-> ProgressDecisive]
ProgressController(mode, behavior) ==
    IF mode = "external-scheduler" /\ behavior = "schedule-sequential"
      THEN "job-controller"
    ELSE "sequential-authority"

ProgressControls(mode) ==
    [frame \in {ProgressFrame} |->
        [principal \in Principals |->
            {behavior \in ProgressDecisive :
                ProgressController(mode, behavior) = principal}]]
ProgressExcludes ==
    [frame \in {ProgressFrame} |-> [principal \in Principals |-> {}]]
ProgressOwners(mode) ==
    {<<ProgressFrame, principal>> :
        principal \in
            ({"sequential-authority"} \cap
             EligibleOwners(ProgressFrame, Principals,
                 ProgressDecisiveOf, ProgressControls(mode), ProgressExcludes))}

ProgressAuthorityHeld ==
    /\ ProgressOwners("owned-scheduler") =
         {<<ProgressFrame, "sequential-authority">>}
    /\ ProgressOwners("external-scheduler") = {}
    /\ \A mode \in {"owned-scheduler", "external-scheduler"} :
          CompleteOwnershipDisposition(
              {ProgressFrame}, Principals, ProgressOwners(mode),
              ProgressDecisiveOf, ProgressControls(mode), ProgressExcludes)

VARIABLE progressControl
progressVars == <<vars, progressControl>>

ProgressInit == Init /\ progressControl = "none"
ProgressNext ==
    /\ SequentialStep
    /\ UNCHANGED progressControl

UnfairProgressSpec == ProgressInit /\ [][ProgressNext]_progressVars
ProgressSpec ==
    /\ UnfairProgressSpec
    /\ WF_progressVars(ProgressNext)

ProgressRank ==
    2 * (2 - sequential_pc) - (IF sequential_active THEN 1 ELSE 0)

WriterOwnershipClaimHeld ==
    IF progressControl = "writer-as-owner"
      THEN <<ProgressFrame, "sequential-authority">>
             \in ProgressOwners("external-scheduler")
    ELSE TRUE

ProgressInvariant ==
    /\ ClaimInstantiationHeld
    /\ ProgressAuthorityHeld
    /\ progressControl \in {"none", "writer-as-owner"}
    /\ ProgressRank \in 0..4
    /\ WriterOwnershipClaimHeld

EventualSequentialCompletion == <> (sequential_pc = 2 /\ ~sequential_active)
====
