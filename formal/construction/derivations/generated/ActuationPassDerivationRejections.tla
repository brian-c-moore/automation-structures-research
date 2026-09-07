---- MODULE ActuationPassDerivationRejections ----
EXTENDS ActuationPassDerivationData, TLC

WithdrawAfterEffect == {<<"actuated", "wrong-effect">>}

WithdrawAfterEffectWitness ==
    [Derivation EXCEPT
        !.witnessEnvironmentSteps =
            @ \cup WithdrawAfterEffect,
        !.witnessRelySteps =
            @ \cup WithdrawAfterEffect]

PromotedAssuranceMap ==
    [action \in Derivation.canonicalActions |->
        IF action \in DOMAIN Derivation.assuranceAt
          THEN Derivation.assuranceAt[action]
          ELSE "at-commit"]

PromotedEnvironmentRecord ==
    [Derivation EXCEPT
        !.systemActions = Derivation.canonicalActions,
        !.environmentActions = {},
        !.commitActions = Derivation.canonicalActions,
        !.assuranceAt = PromotedAssuranceMap]

RejectsWithdrawAfterEffect ==
    ~DerivationRecordAccepted(WithdrawAfterEffectWitness)

\* Even with an assurance value added, provider-owned allocation changes are
\* not silently accepted as pass-owned commits: the witness commit/ownership
\* surface remains the smaller exact pass boundary.
RejectsEnvironmentPromotion ==
    ~DerivationRecordAccepted(PromotedEnvironmentRecord)

DerivationInit == progressState = "actuation-rejection"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
