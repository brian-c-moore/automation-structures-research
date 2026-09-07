---- MODULE ALKClaimRelationalWitness ----
EXTENDS Naturals, Sequences, ClaimRelativeOwnership

VARIABLES leftPc, leftValue, leftActive, leftHistory,
          rightPc, rightValue, rightActive, rightHistory

leftVars == <<leftPc, leftValue, leftActive, leftHistory>>
rightVars == <<rightPc, rightValue, rightActive, rightHistory>>
pairVars == <<leftVars, rightVars>>

Left == INSTANCE Sequential WITH Steps <- 2, ValueDomain <- {0, 1},
    pc <- leftPc, value <- leftValue, active <- leftActive, history <- leftHistory
Right == INSTANCE Sequential WITH Steps <- 2, ValueDomain <- {0, 1},
    pc <- rightPc, value <- rightValue, active <- rightActive, history <- rightHistory

\* A bounded self-composition, not arbitrary trace equivalence or secrecy.
\* The two canonical carriers take matched begin/complete actions and the
\* same nondeterministic value at each completion. The owning protocol must
\* control that joint choice; neither individual writer alone suffices.
RelationalFrame ==
    [subject |-> "two-sequential-carriers",
     obligation |-> "matched-completion-history-agreement",
     mode |-> "lockstep-coupled-values",
     scope |-> "two-steps-values-zero-or-one",
     observationBoundary |-> "paired-completed-histories",
     authorityBoundary |-> "joint-value-choice-and-paired-commit",
     claimant |-> "observer",
     failureModel |-> "atomic-pair-no-crash-no-independent-value-writer",
     abstraction |-> "self-composed-sequential-carriers",
     lifecyclePhase |-> "execution",
     propertyForm |-> "relational"]

PairPrincipals == {"left-controller", "right-controller", "pair-protocol", "observer"}
PairMembers == {"left-controller", "right-controller"}
PairBehaviors == {"left-completion-choice", "right-completion-choice", "paired-admission"}
PairDecisiveOf == [frame \in {RelationalFrame} |-> PairBehaviors]
PairController(mode, behavior) ==
    IF mode = "protocol" THEN "pair-protocol"
    ELSE CASE behavior = "left-completion-choice" -> "left-controller"
           [] behavior = "right-completion-choice" -> "right-controller"
           [] OTHER -> "observer"
PairControls(mode) ==
    [frame \in {RelationalFrame} |->
        [principal \in PairPrincipals |->
            {behavior \in PairBehaviors : PairController(mode, behavior) = principal}]]
PairExcludes ==
    [frame \in {RelationalFrame} |-> [principal \in PairPrincipals |-> {}]]
PairOwners(mode) ==
    {<<RelationalFrame, principal>> :
        principal \in ({"pair-protocol"} \cap
            EligibleOwners(RelationalFrame, PairPrincipals, PairDecisiveOf,
                           PairControls(mode), PairExcludes))}

PairInit == Left!Init /\ Right!Init
PairBegin == Left!BeginStep /\ Right!BeginStep
PairComplete ==
    /\ Left!CompleteStep
    /\ Right!CompleteStep
    /\ leftValue' = rightValue'
PairDone == Left!DoneStuttering /\ Right!DoneStuttering
PairNext == PairBegin \/ PairComplete \/ PairDone
AuthorizedPairStep(actor, decision) ==
    /\ actor = "pair-protocol"
    /\ decision = PairMembers
    /\ PairNext
PairSpec ==
    PairInit /\ [][AuthorizedPairStep("pair-protocol", PairMembers)]_pairVars

BothCatalogContractsHeld ==
    /\ Left!TypeInvariant /\ Left!HistoryPositionAgreement
    /\ Right!TypeInvariant /\ Right!HistoryPositionAgreement
MatchedHistoryHeld ==
    /\ leftPc = rightPc
    /\ leftActive = rightActive
    /\ leftHistory = rightHistory
RelationalAuthorityHeld ==
    /\ PairOwners("protocol") = {<<RelationalFrame, "pair-protocol">>}
    /\ PairOwners("independent-writers") = {}
PairInvariant ==
    /\ BothCatalogContractsHeld
    /\ MatchedHistoryHeld
    /\ RelationalAuthorityHeld
====
