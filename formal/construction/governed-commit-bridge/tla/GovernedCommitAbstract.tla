---------------------- MODULE GovernedCommitAbstract ----------------------
EXTENDS Naturals, Integers

AbstractPhases == {"pending", "active", "recovering", "committed", "failed"}
ActionClasses == {"init", "system", "commit", "failure", "stutter"}

AbstractType(a) ==
    /\ a.phase \in AbstractPhases
    /\ a.capacity \in Nat
    /\ a.used \in Nat
    /\ a.used <= a.capacity
    /\ a.effect \in BOOLEAN
    /\ a.audited \in BOOLEAN
    /\ a.recovery \in BOOLEAN
    /\ a.lastClass \in ActionClasses

AbstractInit(a) ==
    /\ AbstractType(a)
    /\ a.phase = "pending"
    /\ a.used = 0
    /\ ~a.effect
    /\ ~a.audited
    /\ ~a.recovery
    /\ a.lastClass = "init"

AbstractSystemStep(a, b) ==
    /\ b.lastClass = "system"
    /\ b.capacity = a.capacity
    /\ b.effect = a.effect
    /\ b.audited = a.audited
    /\ b.recovery = a.recovery
    /\ \/ /\ a.phase = "pending"
          /\ b.phase = "active"
          /\ b.used = 1
       \/ /\ a.phase = "active"
          /\ b.phase = "active"
          /\ b.used = a.used

AbstractFailureStep(a, b) ==
    /\ b.lastClass = "failure"
    /\ b.capacity = a.capacity
    /\ \/ /\ b.phase = "failed"
          /\ b.used = a.used
          /\ b.effect = a.effect
          /\ b.audited = a.audited
          /\ b.recovery = a.recovery
       \/ /\ a.phase = "active"
          /\ b.phase = "active"
          /\ b.used = a.used
          /\ b.effect = a.effect
          /\ b.audited = a.audited
          /\ b.recovery = a.recovery
       \/ /\ a.phase = "active"
          /\ b.phase = "recovering"
          /\ b.used = a.used
          /\ b.effect
          /\ ~b.audited
          /\ b.recovery
       \/ /\ b.phase = a.phase
          /\ b.used = a.used
          /\ b.effect = a.effect
          /\ b.audited = a.audited
          /\ b.recovery = a.recovery

AbstractCommitStep(a, b) ==
    /\ b.lastClass = "commit"
    /\ a.phase \in {"active", "recovering"}
    /\ b.phase = "committed"
    /\ b.capacity = a.capacity
    /\ b.used = 1
    /\ b.effect
    /\ b.audited
    /\ ~b.recovery

AbstractStutterStep(a, b) ==
    /\ b.lastClass = "stutter"
    /\ b.phase = a.phase
    /\ b.capacity = a.capacity
    /\ b.used = a.used
    /\ b.effect = a.effect
    /\ b.audited = a.audited
    /\ b.recovery = a.recovery

AbstractStep(a, b) ==
    \/ AbstractSystemStep(a, b)
    \/ AbstractFailureStep(a, b)
    \/ AbstractCommitStep(a, b)
    \/ AbstractStutterStep(a, b)

AbstractObservation(a) ==
    [externalEffect |-> a.effect,
     committed     |-> a.phase = "committed",
     audited       |-> a.audited,
     failed        |-> a.phase \in {"failed", "recovering"}]

AbstractGuarantee(a) ==
    /\ a.used <= a.capacity
    /\ (a.phase = "committed" => a.audited)

=============================================================================
