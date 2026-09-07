---- MODULE ALKClaimAssuranceBinding_Proof ----
EXTENDS ALKClaimAssuranceBindingWitness, TLAPS

THEOREM DiagnosticPartitionExact == DiagnosticNext <=> EvidenceNext
  <1>1. \A label \in DiagnosticLabels :
          DiagnosticGate(label, DiagnosticController(label), DiagnosticDecision(label))
            <=> DiagnosticAction(label)
    BY DEF DiagnosticGate
  <1>2. (\E label \in DiagnosticLabels : DiagnosticAction(label)) <=> EvidenceNext
    BY DEF DiagnosticLabels, DiagnosticAction, EvidenceNext
  <1> QED BY <1>1, <1>2 DEF DiagnosticNext

THEOREM DiagnosticGateRejectsOtherActor ==
    \A label \in DiagnosticLabels :
      \A actor \in Principals :
        \A decision \in SUBSET Principals :
          actor # DiagnosticController(label) =>
            ~DiagnosticGate(label, actor, decision)
BY DEF DiagnosticGate

THEOREM DiagnosticGateRequiresCompleteDecision ==
    \A label \in DiagnosticLabels :
      \A actor \in Principals :
        \A decision \in SUBSET Principals :
          decision # DiagnosticDecision(label) =>
            ~DiagnosticGate(label, actor, decision)
BY DEF DiagnosticGate

THEOREM DiagnosticOwnerControlsBoundActions ==
    \A pair \in DiagnosticOwnership :
      \A label \in DiagnosticDecisiveOf[pair[1]] :
        DiagnosticController(label) = pair[2]
BY SMT DEF DiagnosticOwnership, EligibleOwners, Covers,
           DiagnosticControls, DiagnosticExcludes

====
