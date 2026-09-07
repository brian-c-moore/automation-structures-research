---- MODULE ALKClaimAuthorityModel ----
EXTENDS ALKClaimFrameData

\* Static mechanism bindings; ALKClaimAuthorityBinding applies the gates
\* to actual catalog transitions and proves the partition exact.
Principals ==
    {"budget-authority", "sequential-authority", "job-controller",
     "budget-worker", "successor-authority", "alk-protocol",
     "independent-auditor", "recovery-provider"}

Behaviors == CatalogBehaviors \cup {"worker-compute"}
AuthorityModes == {"direct", "work", "transfer", "split", "protocol"}
ProtocolMembers == {"budget-authority", "successor-authority"}

Mechanisms ==
    {"budget-guard", "sequential-state-machine", "worker-runtime",
     "claim-log", "independent-monitor", "recovery-copy",
     "successor-guard", "protocol-guard"}

MechanismController ==
    [mechanism \in Mechanisms |->
        CASE mechanism \in {"budget-guard", "claim-log"} -> "budget-authority"
          [] mechanism = "sequential-state-machine" -> "sequential-authority"
          [] mechanism = "worker-runtime" -> "budget-worker"
          [] mechanism = "independent-monitor" -> "independent-auditor"
          [] mechanism = "recovery-copy" -> "recovery-provider"
          [] mechanism = "protocol-guard" -> "alk-protocol"
          [] OTHER -> "successor-authority"]

BudgetAdmissionBehaviors ==
    {"budget-try-allocate", "budget-reserve", "budget-commit-reservation"}

MechanismOfBehavior(mode, behavior) ==
    IF behavior \in BudgetBehaviors
      THEN CASE mode = "transfer" -> "successor-guard"
             [] mode = "protocol" -> "protocol-guard"
             [] mode = "split" /\ behavior \notin BudgetAdmissionBehaviors ->
                  "successor-guard"
             [] OTHER -> "budget-guard"
      ELSE IF behavior \in SequentialBehaviors \cup {"sequential-done"}
        THEN "sequential-state-machine"
      ELSE "worker-runtime"

ControllerOfBehavior(mode, behavior) ==
    MechanismController[MechanismOfBehavior(mode, behavior)]

RequiredDecision(mode, behavior) ==
    IF mode = "protocol" /\ behavior \in BudgetBehaviors
      THEN ProtocolMembers
    ELSE {ControllerOfBehavior(mode, behavior)}

\* Principal labels denote authenticated identities in this closed model.
\* Mapping an external identity, permission, or executable write path to this
\* relation is a separate conformance premise.
AuthorizationValid(mode, actor, decision, behavior) ==
    /\ mode \in AuthorityModes
    /\ actor \in Principals
    /\ behavior \in CatalogBehaviors
    /\ decision \subseteq Principals
    /\ actor = ControllerOfBehavior(mode, behavior)
    /\ decision = RequiredDecision(mode, behavior)

DecisiveOf ==
    [frame \in Frames |-> DecisiveBehaviorOfSchema[frame.obligation]]

ControlsForMode(mode) ==
    [frame \in Frames |->
      [principal \in Principals |->
        {behavior \in DecisiveOf[frame] :
           ControllerOfBehavior(mode, behavior) = principal}]]

ExcludesOf ==
    [frame \in Frames |-> [principal \in Principals |-> {}]]

AccountabilityNominees(mode, frame) ==
    IF frame = SequentialFrame THEN {"sequential-authority"}
    ELSE CASE mode = "transfer" -> {"successor-authority"}
           [] mode = "protocol" -> {"alk-protocol"}
           [] mode = "split" -> {}
           [] OTHER -> {"budget-authority"}

DerivedOwnership(mode) ==
    {pair \in Frames \X Principals :
       /\ pair[2] \in AccountabilityNominees(mode, pair[1])
       /\ pair[2] \in EligibleOwners(
            pair[1], Principals, DecisiveOf, ControlsForMode(mode), ExcludesOf)}

====
