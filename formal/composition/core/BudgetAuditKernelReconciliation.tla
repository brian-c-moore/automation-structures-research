---- MODULE BudgetAuditKernelReconciliation ----
\* Maps the bounded Budget/audit-presence composition into the
\* composition kernel. CommitRel is shared because it changes the budget ledger
\* and the audit-presence observation in one transition. This module does not
\* identify the boolean audit observation with the full AuditSink log/hash state.

EXTENDS BudgetAuditAssumeGuarantee, CompositionKernel, TLC

InitialStates ==
    {s \in States :
        /\ s.phase = "Ready"
        /\ s.used = 0
        /\ s.reserved = 0
        /\ s.committed = FALSE
        /\ s.audited = FALSE}

BudgetComponentSteps == BudgetStep
AuditComponentSteps == {}
SharedCommitSteps == CommitRel
EnvironmentSteps == {}
FailureSteps == {}
InterferenceSteps == SharedCommitSteps

\* Once CommitRel is classified as shared, the audit component relies only on
\* the budget-owned reserve/reject/terminal relation. Shared preservation is a
\* separate kernel premise, not a peer-rely edge.
KernelBudgetRely == {}
KernelAuditRely == BudgetComponentSteps
KernelRelyEdges == {<<"component-b", "component-a">>}

Providers == {"budget-authority", "audit-owner"}
UnavailableProviders == {}

MappedConcreteStep ==
    ComposedSteps(
        BudgetComponentSteps, AuditComponentSteps, SharedCommitSteps,
        EnvironmentSteps, FailureSteps)

KernelPremises ==
    CompositionSafetyPremises(
        States, InitialStates, BudgetStates, AuditStates,
        BudgetComponentSteps, AuditComponentSteps, SharedCommitSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        KernelBudgetRely, KernelAuditRely, KernelRelyEdges,
        Providers, UnavailableProviders)

KernelConclusion ==
    CompositionSafetyConclusion(
        States, InitialStates, BudgetStates, AuditStates,
        BudgetComponentSteps, AuditComponentSteps, SharedCommitSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps)

VARIABLE marker
vars == <<marker>>

Init == marker = "mapping-witness"

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

====
