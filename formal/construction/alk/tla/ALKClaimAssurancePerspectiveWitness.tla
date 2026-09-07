---- MODULE ALKClaimAssurancePerspectiveWitness ----
EXTENDS ALKClaimAssuranceBindingWitness

\* Change the complete claimant perspective coherently, leaving the actual
\* capture, predicate, owner, and all producer/observation metadata intact.
PerspectiveFrame ==
    IF bindingFault = "owner-as-claimant"
      THEN [BudgetFrame EXCEPT !.claimant = "budget-authority"]
    ELSE BudgetFrame
PerspectiveFrames == {PerspectiveFrame}
PerspectiveOwnership ==
    {<<PerspectiveFrame, "budget-authority">>} \cup
      (IF bindingFault = "shared-owner" THEN {<<PerspectiveFrame, "independent-auditor">>} ELSE {})
PerspectiveRecords ==
    [id \in {"A5"} |-> [BindingRecords[id] EXCEPT
        !.frame = PerspectiveFrame, !.claimant = PerspectiveFrame.claimant,
        !.mechanismFrame = PerspectiveFrame]]
PerspectiveEvidence ==
    [id \in {"A5"} |-> [BindingEvidence[id] EXCEPT
        !.frame = PerspectiveFrame, !.claimant = PerspectiveFrame.claimant]]
PerspectiveGuarantees ==
    [id \in {"A5"} |-> [BindingGuarantees[id] EXCEPT
        !.frame = PerspectiveFrame, !.recipient = PerspectiveFrame.claimant]]
PerspectiveEvidenceSemantics ==
    [id \in {"A5"} |-> BindingEvidenceSemantics[id]]
PerspectiveGuaranteeSemantics ==
    [id \in {"A5"} |-> BindingGuaranteeSemantics[id]]

PerspectiveAdjacentHeld ==
    /\ BindingInvariant
    /\ IF "A5" \in ActiveClasses THEN
          /\ OwnersOf(PerspectiveFrame, Principals, PerspectiveOwnership) = {"budget-authority"}
          /\ PerspectiveRecords["A5"].source = "budget-authority"
          /\ PerspectiveRecords["A5"].claimant = PerspectiveFrame.claimant
          /\ PerspectiveRecords["A5"].mechanismFrame = PerspectiveFrame
          /\ BoundGuarantee(PerspectiveGuarantees["A5"], PerspectiveFrames,
                 Principals, PerspectiveOwnership, PerspectiveGuaranteeSemantics)
          /\ BoundEvidence(PerspectiveRecords["A5"], PerspectiveEvidence["A5"],
                 PerspectiveEvidenceSemantics)
        ELSE TRUE
PerspectiveBindingHeld ==
    IF "A5" \in ActiveClasses THEN
      BoundClaimRecords(PerspectiveFrames, Principals, PerspectiveOwnership,
          PerspectiveRecords, PerspectiveEvidence, PerspectiveEvidenceSemantics,
          PerspectiveGuarantees, PerspectiveGuaranteeSemantics)
    ELSE TRUE
\* Even when CHOOSE happens to return the real issuer, a second declared
\* owner is invalid. The adjacent evidence and chosen guarantee still hold.
AmbiguousPerspectiveAdjacent ==
    /\ BindingInvariant
    /\ IF "A5" \in ActiveClasses THEN
          /\ PerspectiveRecords["A5"].claimant = PerspectiveFrame.claimant
          /\ BoundGuarantee(PerspectiveGuarantees["A5"], PerspectiveFrames,
                 Principals, PerspectiveOwnership, PerspectiveGuaranteeSemantics)
          /\ BoundEvidence(PerspectiveRecords["A5"], PerspectiveEvidence["A5"],
                 PerspectiveEvidenceSemantics)
        ELSE TRUE
====
