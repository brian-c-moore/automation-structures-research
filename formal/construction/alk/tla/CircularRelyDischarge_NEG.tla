---- MODULE CircularRelyDischarge_NEG ----
EXTENDS ALKSemanticModelWitness

CyclicRelyEdges ==
    {<<"audit", "commit">>, <<"commit", "audit">>}
CyclicRelyPropertyClassOf ==
    [edge \in CyclicRelyEdges |-> RelyPropertyClassOf[edge]]

RelyDischarged ==
    RelyDischargeBoundaryTyped(
        States, Components, CyclicRelyEdges, RelyRank,
        CyclicRelyPropertyClassOf, {},
        ComponentObligationStates,
        ComponentRelySteps, ComponentGuaranteeSteps,
        SharedStepsForRelyEdge)

NegativeControlExpected == NegativeControlGate(RelyDischarged)

====
