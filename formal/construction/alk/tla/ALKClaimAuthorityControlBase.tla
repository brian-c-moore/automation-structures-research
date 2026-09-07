---- MODULE ALKClaimAuthorityControlBase ----
EXTENDS ALKClaimAuthorityWitness

ControlModes ==
    {"none", "wrong-controller", "shared-owner", "issuer-mismatch",
     "assurance-ownership", "tcb-promotion", "wrong-claimant",
     "split-owner", "work-transfer"}

VARIABLE controlMode

controlVars == <<vars, controlMode>>

ControlInit ==
    /\ Init
    /\ controlMode = "none"

GoodNext ==
    /\ Next
    /\ UNCHANGED controlMode

Inject(mode) ==
    /\ controlMode = "none"
    /\ mode \in ControlModes \ {"none"}
    /\ controlMode' = mode
    /\ UNCHANGED vars

ControlSpec == ControlInit /\ [][GoodNext]_controlVars

EffectiveOwnership ==
    CASE controlMode = "wrong-controller" ->
           {<<BudgetFrame, "sequential-authority">>,
            <<SequentialFrame, "sequential-authority">>}
      [] controlMode = "shared-owner" ->
           Ownership \cup {<<BudgetFrame, "successor-authority">>}
      [] controlMode = "assurance-ownership" ->
           (Ownership \ {<<BudgetFrame, "budget-authority">>})
             \cup {<<BudgetFrame, "job-controller">>}
      [] controlMode \in {"tcb-promotion", "work-transfer"} ->
           (Ownership \ {<<BudgetFrame, "budget-authority">>})
             \cup {<<BudgetFrame, "budget-worker">>}
      [] OTHER -> Ownership

EffectiveControlsOf ==
    [frame \in Frames |->
      [principal \in Principals |->
        IF /\ controlMode = "shared-owner"
           /\ frame = BudgetFrame
           /\ principal \in {"budget-authority", "successor-authority"}
          THEN DecisiveOf[frame]
        ELSE IF controlMode = "split-owner"
          THEN SplitControlsOf[frame][principal]
        ELSE ControlsOf[frame][principal]]]

EffectiveGuaranteeIssuer ==
    [guarantee \in Guarantees |->
        IF /\ controlMode = "issuer-mismatch"
           /\ guarantee = "g-budget"
          THEN "sequential-authority"
        ELSE GuaranteeIssuer[guarantee]]

EffectiveAssuranceClaimant ==
    [assurance \in Assurances |->
        IF /\ controlMode = "wrong-claimant"
           /\ assurance = "a5"
          THEN "independent-auditor"
        ELSE AssuranceClaimant[assurance]]

OwnershipControlHeld ==
    OwnershipBoundaryHeld(EffectiveOwnership, EffectiveControlsOf)

IssuerControlHeld ==
    GuaranteeBoundaryHeld(
        Ownership, EffectiveGuaranteeIssuer, GuaranteeRecipient)

ClaimantControlHeld ==
    AssuranceProfileBoundaryHeld(EffectiveAssuranceClaimant)

WorkDelegationControlHeld ==
    /\ DelegationKind["d-budget-work"] = "work"
    /\ OwnershipBoundaryHeld(EffectiveOwnership, EffectiveControlsOf)

ControlFrameHeld ==
    /\ controlMode \in ControlModes
    /\ ClaimInstantiationHeld

ControlInvariant ==
    /\ ControlFrameHeld
    /\ OwnershipControlHeld
    /\ IssuerControlHeld
    /\ ClaimantControlHeld
    /\ WorkDelegationControlHeld

====
