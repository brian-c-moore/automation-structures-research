---- MODULE BudgetAuditComposition ----
EXTENDS Naturals, TLC

CONSTANTS Capacity, MaxRequest,
          NoFault, NoAudit, Overspend,
          FaultMode

ASSUME Capacity \in Nat \ {0}
ASSUME MaxRequest \in Nat \ {0}
ASSUME FaultMode \in {NoFault, NoAudit, Overspend}

VARIABLES phase, request, used, reserved, committed, audited
vars == <<phase, request, used, reserved, committed, audited>>

Init ==
    /\ phase = "Ready"
    /\ request \in 1..MaxRequest
    /\ used = 0
    /\ reserved = 0
    /\ committed = FALSE
    /\ audited = FALSE

Reserve ==
    /\ phase = "Ready"
    /\ request <= Capacity - used \/ FaultMode = Overspend
    /\ phase' = "Reserved"
    /\ reserved' = request
    /\ UNCHANGED <<request, used, committed, audited>>

Reject ==
    /\ phase = "Ready"
    /\ request > Capacity - used
    /\ FaultMode /= Overspend
    /\ phase' = "Done"
    /\ UNCHANGED <<request, used, reserved, committed, audited>>

Commit ==
    /\ phase = "Reserved"
    /\ phase' = "Done"
    /\ used' = used + reserved
    /\ reserved' = 0
    /\ committed' = TRUE
    /\ audited' = (FaultMode /= NoAudit)
    /\ UNCHANGED request

Done ==
    /\ phase = "Done"
    /\ UNCHANGED vars

Next == Reserve \/ Reject \/ Commit \/ Done
Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ phase \in {"Ready", "Reserved", "Done"}
    /\ request \in 1..MaxRequest
    /\ used \in Nat
    /\ reserved \in Nat
    /\ committed \in BOOLEAN
    /\ audited \in BOOLEAN

BudgetInvariant == used + reserved <= Capacity
AuditInvariant == committed => audited
CompositionInvariant == BudgetInvariant /\ AuditInvariant

====
