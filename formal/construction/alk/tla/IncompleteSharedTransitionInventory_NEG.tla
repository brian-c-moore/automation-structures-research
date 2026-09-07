---- MODULE IncompleteSharedTransitionInventory_NEG ----
EXTENDS ALKConstructionTheoremWitness

IncompleteRegisteredSharedSteps == {}
IncompleteAffectedComponents == {"component-a"}

IncompleteRelationInventoryHeld ==
    ExactSharedTransitionBoundary(
        States, Components, RepresentedSharedSteps,
        IncompleteRegisteredSharedSteps, AffectedComponents,
        ComponentObligationStates)

IncompleteAffectedInventoryHeld ==
    ExactSharedTransitionBoundary(
        States, Components, RepresentedSharedSteps,
        RegisteredSharedSteps, IncompleteAffectedComponents,
        ComponentObligationStates)

ExactSharedTransitionInventoryHeld ==
    IncompleteRelationInventoryHeld
      \/ IncompleteAffectedInventoryHeld

NegativeControlExpected == NegativeControlGate(ExactSharedTransitionInventoryHeld)

====
