---- MODULE Sequential ----
\* Sequential carrier: one active locus advances a program counter and value.
\* HistoryPositionAgreement checks that history and completed-step count remain
\* aligned.
\* Parallelism degree one and absence of branching are representation ceilings:
\* this carrier has one active flag and one program counter.
EXTENDS Naturals, Sequences

CONSTANTS Steps, ValueDomain
\* Steps        : positive natural — number of steps in the program
\* ValueDomain  : finite set of possible values

\* Init picks the starting value with CHOOSE over ValueDomain, and CHOOSE over
\* an empty set is not defined, so the non-emptiness the module relies on is
\* stated here rather than left to whichever model binds the constant.
ASSUME ValueDomainNonEmpty == ValueDomain # {}
ASSUME StepsType == Steps \in Nat /\ Steps > 0

VARIABLES pc, value, active, history

vars == <<pc, value, active, history>>

TypeInvariant ==
    /\ pc \in 0..Steps
    /\ value \in ValueDomain
    /\ active \in BOOLEAN
    /\ history \in Seq(ValueDomain)

Init ==
    /\ pc      = 0
    /\ value   = CHOOSE v \in ValueDomain : TRUE
    /\ active  = FALSE
    /\ history = <<>>

\* BeginStep: enter the active state. Only one step is active.
BeginStep ==
    /\ pc < Steps
    /\ ~active
    /\ active'  = TRUE
    /\ UNCHANGED <<pc, value, history>>

\* CompleteStep: apply the function (modeled as nondeterministic value
\* update), advance counter, leave active state, append to history.
CompleteStep ==
    /\ active
    /\ \E v \in ValueDomain :
        /\ value'   = v
        /\ history' = Append(history, v)
    /\ pc'     = pc + 1
    /\ active' = FALSE

DoneStuttering ==
    /\ pc = Steps
    /\ ~active
    /\ UNCHANGED vars

Next == BeginStep \/ CompleteStep \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* The history length tracks the completed-step count. Both branches reduce to
\* Len(history) = pc: BeginStep frames pc and history, while CompleteStep
\* advances pc and appends history atomically.
HistoryPositionAgreement ==
    \/ (~active /\ Len(history) = pc)
    \/ ( active /\ Len(history) = pc)

\* Compatibility alias only. The formula does not compare arbitrary events and
\* therefore does not establish a general total-order property.
TotalOrder == HistoryPositionAgreement
====
