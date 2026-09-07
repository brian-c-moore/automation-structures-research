---- MODULE AssumeGuaranteeRule_OmittedRely_NEG ----
\* Necessity control for StepB \subseteq RelyA. The mutant contract omits that
\* premise. B's 0->1 step then satisfies its own invariant but violates A's
\* invariant, so the composed invariant is not stable.

EXTENDS Naturals

VARIABLE controlState
vars == <<controlState>>

S == {0, 1}
InvA == {0}
InvB == S
StepA == {}
StepB == {<<0, 1>>}
RelyA == {}
RelyB == StepA

Stable(Inv, Rel) ==
    \A s \in Inv, t \in S : <<s, t>> \in Rel => t \in Inv

\* Fault: the StepB-subset-of-RelyA premise is absent.
OmittedRelyContract ==
    /\ Stable(InvA, StepA \cup RelyA)
    /\ Stable(InvB, StepB \cup RelyB)
    /\ StepA \subseteq RelyB

Init == controlState = 0 /\ OmittedRelyContract
Next ==
    /\ <<0, 1>> \in StepA \cup StepB
    /\ controlState = 0
    /\ controlState' = 1
Spec == Init /\ [][Next]_vars

ComposedInvariant == controlState \in InvA \cap InvB
====
