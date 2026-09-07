---- MODULE AssumeGuaranteeRule ----
EXTENDS FiniteSets

CONSTANTS S, InvA, InvB, StepA, StepB, RelyA, RelyB

Pairs == S \X S

Stable(Inv, Rel) ==
    \A s \in Inv, t \in S : <<s, t>> \in Rel => t \in Inv

WellTyped ==
    /\ InvA \subseteq S
    /\ InvB \subseteq S
    /\ StepA \subseteq Pairs
    /\ StepB \subseteq Pairs
    /\ RelyA \subseteq Pairs
    /\ RelyB \subseteq Pairs

Contract ==
    /\ WellTyped
    /\ Stable(InvA, StepA \cup RelyA)
    /\ Stable(InvB, StepB \cup RelyB)
    /\ StepA \subseteq RelyB
    /\ StepB \subseteq RelyA

ComposedInvariant == InvA \cap InvB
ComposedStep == StepA \cup StepB

====
