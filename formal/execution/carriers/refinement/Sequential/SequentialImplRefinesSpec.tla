---- MODULE SequentialImplRefinesSpec ----
(***************************************************************************)
(* Executable-contract transcription for the finite Sequential carrier.    *)
(* Each accepted method call maps to one canonical action; rejected calls  *)
(* and the terminal observation stutter under the identity state mapping.  *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, Sequences

CONSTANTS Steps, ValueDomain
ASSUME ValueDomainNonEmpty == ValueDomain # {}
ASSUME StepsType == Steps \in Nat /\ Steps > 0

VARIABLES pc, value, active, history
vars == <<pc, value, active, history>>

ImplInvariant ==
    /\ pc \in 0..Steps
    /\ value \in ValueDomain
    /\ active \in BOOLEAN
    /\ history \in Seq(ValueDomain)
    /\ Len(history) = pc

Init ==
    /\ pc = 0
    /\ value = CHOOSE v \in ValueDomain : TRUE
    /\ active = FALSE
    /\ history = <<>>

ImplBeginStep ==
    /\ pc < Steps
    /\ ~active
    /\ active' = TRUE
    /\ UNCHANGED <<pc, value, history>>

ImplCompleteStep(v) ==
    /\ active
    /\ v \in ValueDomain
    /\ value' = v
    /\ history' = Append(history, v)
    /\ pc' = pc + 1
    /\ active' = FALSE

ImplDoneStuttering ==
    /\ pc = Steps
    /\ ~active
    /\ UNCHANGED vars

ImplNext ==
    \/ ImplBeginStep
    \/ \E v \in ValueDomain : ImplCompleteStep(v)
    \/ ImplDoneStuttering

S == INSTANCE Sequential WITH
        Steps <- Steps,
        ValueDomain <- ValueDomain,
        pc <- pc,
        value <- value,
        active <- active,
        history <- history

Spec == Init /\ [][ImplNext]_vars
Refinement == S!Spec
====

