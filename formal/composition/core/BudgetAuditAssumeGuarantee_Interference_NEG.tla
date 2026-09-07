---- MODULE BudgetAuditAssumeGuarantee_Interference_NEG ----
\* Concrete interference control. The audit-owned commit adds one unit beyond
\* the reserved amount, violating the budget invariant. This is the exact
\* cross-component stability obligation discharged by BudgetStableProof.

EXTENDS BudgetAuditAssumeGuarantee

VARIABLE current
vars == <<current>>

Init ==
    current = [phase     |-> "Reserved",
               request   |-> 1,
               used      |-> 1,
               reserved  |-> 1,
               committed |-> FALSE,
               audited   |-> FALSE]

BadAuditCommit ==
    /\ current.phase = "Reserved"
    /\ current' = [phase     |-> "Done",
                   request   |-> current.request,
                   used      |-> current.used + current.reserved + 1,
                   reserved  |-> 0,
                   committed |-> TRUE,
                   audited   |-> TRUE]

Next == BadAuditCommit
Spec == Init /\ [][Next]_vars

ConcreteCompositionInvariant == current \in BudgetStates \cap AuditStates
====
