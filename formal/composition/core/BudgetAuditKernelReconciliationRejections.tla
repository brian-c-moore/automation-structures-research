---- MODULE BudgetAuditKernelReconciliationRejections ----
\* Mapping-specific false-credit controls. The first omits the audit rely while
\* retaining its declared edge. The second mutates the shared commit so it
\* overspends while still recording audit presence.

EXTENDS BudgetAuditKernelReconciliation, TLC

OmittedAuditRelyPremises ==
    CompositionSafetyPremises(
        States, InitialStates, BudgetStates, AuditStates,
        BudgetComponentSteps, AuditComponentSteps, SharedCommitSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        KernelBudgetRely, {}, KernelRelyEdges,
        Providers, UnavailableProviders)

BadSharedCommitSteps ==
    {p \in Pairs :
        LET s == p[1]
            t == p[2]
        IN  /\ s.phase = "Reserved"
            /\ t.phase = "Done"
            /\ t.request = s.request
            /\ t.used = s.used + s.reserved
            /\ t.reserved = s.reserved
            /\ t.committed = TRUE
            /\ t.audited = TRUE}

BadSharedInterferencePremises ==
    CompositionSafetyPremises(
        States, InitialStates, BudgetStates, AuditStates,
        BudgetComponentSteps, AuditComponentSteps, BadSharedCommitSteps,
        EnvironmentSteps, FailureSteps, BadSharedCommitSteps,
        KernelBudgetRely, KernelAuditRely, KernelRelyEdges,
        Providers, UnavailableProviders)

OmittedRelyRejected == ~OmittedAuditRelyPremises
BadSharedInterferenceRejected == ~BadSharedInterferencePremises

====
