---- MODULE BudgetAuditAssumeGuarantee ----
\* Concrete finite-state instantiation of AssumeGuaranteeRule for the
\* fault-free BudgetAuditComposition transition system. Reserve, Reject, and
\* terminal stuttering are budget-owned; Commit is audit-owned and is the
\* interference that the budget component must admit. The relations below
\* spell out every frame field rather than assuming correspondence by name.

EXTENDS Naturals, FiniteSets

CONSTANTS Capacity, MaxRequest

ASSUME CapacityType == Capacity \in Nat \ {0}
ASSUME MaxRequestType == MaxRequest \in Nat \ {0}

Phases == {"Ready", "Reserved", "Done"}

States ==
    [phase     : Phases,
     request   : 1..MaxRequest,
     used      : 0..Capacity,
     reserved  : 0..Capacity,
     committed : BOOLEAN,
     audited   : BOOLEAN]

Pairs == States \X States

BudgetStates == {s \in States : s.used + s.reserved <= Capacity}
AuditStates == {s \in States : s.committed => s.audited}

ReserveRel ==
    {p \in Pairs :
        LET s == p[1]
            t == p[2]
        IN  /\ s.phase = "Ready"
            /\ s.used + s.request <= Capacity
            /\ t.phase = "Reserved"
            /\ t.request = s.request
            /\ t.used = s.used
            /\ t.reserved = s.request
            /\ t.committed = s.committed
            /\ t.audited = s.audited}

RejectRel ==
    {p \in Pairs :
        LET s == p[1]
            t == p[2]
        IN  /\ s.phase = "Ready"
            /\ s.used + s.request > Capacity
            /\ t.phase = "Done"
            /\ t.request = s.request
            /\ t.used = s.used
            /\ t.reserved = s.reserved
            /\ t.committed = s.committed
            /\ t.audited = s.audited}

CommitRel ==
    {p \in Pairs :
        LET s == p[1]
            t == p[2]
        IN  /\ s.phase = "Reserved"
            /\ t.phase = "Done"
            /\ t.request = s.request
            /\ t.used = s.used + s.reserved
            /\ t.reserved = 0
            /\ t.committed = TRUE
            /\ t.audited = TRUE}

TerminalRel ==
    {p \in Pairs :
        LET s == p[1]
            t == p[2]
        IN  /\ s.phase = "Done"
            /\ t.phase = s.phase
            /\ t.request = s.request
            /\ t.used = s.used
            /\ t.reserved = s.reserved
            /\ t.committed = s.committed
            /\ t.audited = s.audited}

BudgetStep == ReserveRel \cup RejectRel \cup TerminalRel
AuditStep == CommitRel

\* Each component's rely is exactly the other component's guarantee.
BudgetRely == AuditStep
AuditRely == BudgetStep

AG == INSTANCE AssumeGuaranteeRule
        WITH S <- States,
             InvA <- BudgetStates,
             InvB <- AuditStates,
             StepA <- BudgetStep,
             StepB <- AuditStep,
             RelyA <- BudgetRely,
             RelyB <- AuditRely

ComposedInvariantStates == BudgetStates \cap AuditStates
ComposedStepRel == BudgetStep \cup AuditStep

\* Independent direct encoding of the fault-free concrete action disjunction.
\* ActionPartition in the proof module establishes exact equality with the
\* component-owned union, including every guard and frame.
ConcreteNoFaultStep ==
    {p \in Pairs :
        LET s == p[1]
            t == p[2]
        IN  \/ /\ s.phase = "Ready"
                   /\ s.used + s.request <= Capacity
                   /\ t.phase = "Reserved"
                   /\ t.request = s.request
                   /\ t.used = s.used
                   /\ t.reserved = s.request
                   /\ t.committed = s.committed
                   /\ t.audited = s.audited
            \/ /\ s.phase = "Ready"
                   /\ s.used + s.request > Capacity
                   /\ t.phase = "Done"
                   /\ t.request = s.request
                   /\ t.used = s.used
                   /\ t.reserved = s.reserved
                   /\ t.committed = s.committed
                   /\ t.audited = s.audited
            \/ /\ s.phase = "Reserved"
                   /\ t.phase = "Done"
                   /\ t.request = s.request
                   /\ t.used = s.used + s.reserved
                   /\ t.reserved = 0
                   /\ t.committed = TRUE
                   /\ t.audited = TRUE
            \/ /\ s.phase = "Done"
                   /\ t.phase = s.phase
                   /\ t.request = s.request
                   /\ t.used = s.used
                   /\ t.reserved = s.reserved
                   /\ t.committed = s.committed
                   /\ t.audited = s.audited}
====
