---- MODULE EdfPremiseBinding ----
\* Safety model for the composition premises used by FEX-DOM-RT-01.
\*
\* Published scheduling results remain the authority for the implication from
\* feasible processor demand and EDF dispatch to deadline satisfaction. This
\* module checks the construction side of that implication: complete admission,
\* complete readiness, minimum-deadline selection, winner-to-effect identity,
\* one-unit progress, work conservation, and ordered execution positions.

EXTENDS Naturals, FiniteSets

CONSTANTS
    Jobs, Urgent, Later, Horizon, Capacity, RepeatingDemand,
    Demand(_), Release(_), Deadline(_), JobOrder(_), IntervalDemand(_),
    NULL, Fault

Faults == {
    "None",
    "BypassAdmission",
    "OmitReady",
    "ReverseUrgency",
    "IdleReady",
    "MisdirectEffect",
    "SuppressProgress",
    "AccelerateProgress",
    "SkipActuation"
}

ASSUME ModelTypes ==
    /\ IsFiniteSet(Jobs)
    /\ Jobs # {}
    /\ Urgent \in Jobs
    /\ Later \in Jobs
    /\ Urgent # Later
    /\ Horizon \in Nat \ {0}
    /\ Capacity \in Nat
    /\ RepeatingDemand \in Nat
    /\ NULL \notin Jobs
    /\ Fault \in Faults
    /\ \A j \in Jobs :
        /\ Demand(j) \in Nat \ {0}
        /\ Release(j) \in 0..Horizon
        /\ Deadline(j) \in 0..Horizon
        /\ JobOrder(j) \in Nat
    /\ \A i \in 1..Horizon : IntervalDemand(i) \in Nat

VARIABLES
    phase, now, checked, published,
    remaining, spent, beforeRemaining, beforeSpent,
    candidates, winner, effect, charge,
    completed, actuationSteps

vars == <<
    phase, now, checked, published,
    remaining, spent, beforeRemaining, beforeSpent,
    candidates, winner, effect, charge,
    completed, actuationSteps
>>

Intervals == 1..Horizon

ReadyAt(t, rem) ==
    {j \in Jobs : Release(j) <= t /\ rem[j] > 0}

Precedes(left, right) ==
    \/ Deadline(left) < Deadline(right)
    \/ /\ Deadline(left) = Deadline(right)
       /\ JobOrder(left) <= JobOrder(right)

\* Finite values used by the positive model and every paired control. They are
\* ordinary constant-operator overrides, following the same configuration
\* mechanism used by the retained structure models.
ConfiguredDemand(job) == IF job = Urgent THEN 2 ELSE 1
ConfiguredRelease(job) == 0
ConfiguredDeadline(job) == IF job = Urgent THEN 2 ELSE 3
ConfiguredJobOrder(job) == IF job = Urgent THEN 1 ELSE 2
ConfiguredIntervalDemand(interval) ==
    CASE interval = 1 -> 0
      [] interval = 2 -> 2
      [] interval = 3 -> 3
      [] OTHER -> 3

TypeInvariant ==
    /\ phase \in {"admission", "idle", "ready", "selected", "actuated", "done"}
    /\ now \in 0..Horizon
    /\ checked \subseteq Intervals
    /\ published \in BOOLEAN
    /\ remaining \in [Jobs -> Nat]
    /\ spent \in [Jobs -> Nat]
    /\ beforeRemaining \in [Jobs -> Nat]
    /\ beforeSpent \in [Jobs -> Nat]
    /\ candidates \subseteq Jobs
    /\ winner \in Jobs \cup {NULL}
    /\ effect \in Jobs \cup {NULL}
    /\ charge \in Nat
    /\ completed \in 0..Horizon
    /\ actuationSteps \in 0..(Horizon + 1)

AdmissionBinding ==
    published =>
        /\ checked = Intervals
        /\ RepeatingDemand <= Capacity
        /\ \A i \in Intervals : IntervalDemand(i) <= i

ActiveQuantum == phase \in {"ready", "selected", "actuated"}

CompleteReadySet ==
    ActiveQuantum => candidates = ReadyAt(now, beforeRemaining)

WinnerOptimality ==
    phase \in {"selected", "actuated"} /\ winner # NULL =>
        /\ winner \in candidates
        /\ \A job \in candidates : Precedes(winner, job)

WorkConservation ==
    phase \in {"selected", "actuated"} =>
        (winner = NULL <=> candidates = {})

EffectBinding ==
    phase = "actuated" => effect = winner

UnitProgress ==
    phase = "actuated" =>
        IF winner = NULL
        THEN /\ charge = 0
             /\ remaining = beforeRemaining
             /\ spent = beforeSpent
        ELSE /\ charge = 1
             /\ remaining = [beforeRemaining EXCEPT ![winner] = @ - 1]
             /\ spent = [beforeSpent EXCEPT ![winner] = @ + 1]

BudgetConservation ==
    \A job \in Jobs : remaining[job] + spent[job] = Demand(job)

SequentialOrder ==
    /\ completed = now
    /\ completed <= actuationSteps
    /\ actuationSteps <= completed + 1

CompositionInvariant ==
    /\ AdmissionBinding
    /\ CompleteReadySet
    /\ WinnerOptimality
    /\ WorkConservation
    /\ EffectBinding
    /\ UnitProgress
    /\ BudgetConservation
    /\ SequentialOrder

Init ==
    /\ phase = "admission"
    /\ now = 0
    /\ checked = {}
    /\ published = FALSE
    /\ remaining = [j \in Jobs |-> Demand(j)]
    /\ spent = [j \in Jobs |-> 0]
    /\ beforeRemaining = [j \in Jobs |-> Demand(j)]
    /\ beforeSpent = [j \in Jobs |-> 0]
    /\ candidates = {}
    /\ winner = NULL
    /\ effect = NULL
    /\ charge = 0
    /\ completed = 0
    /\ actuationSteps = 0

CheckInterval(i) ==
    /\ phase = "admission"
    /\ i \in Intervals \ checked
    /\ IntervalDemand(i) <= i
    /\ checked' = checked \cup {i}
    /\ UNCHANGED <<
        phase, now, published,
        remaining, spent, beforeRemaining, beforeSpent,
        candidates, winner, effect, charge,
        completed, actuationSteps
        >>

Publish ==
    /\ phase = "admission"
    /\ \/ /\ checked = Intervals
           /\ RepeatingDemand <= Capacity
       \/ Fault = "BypassAdmission"
    /\ published' = TRUE
    /\ phase' = "idle"
    /\ UNCHANGED <<
        now, checked,
        remaining, spent, beforeRemaining, beforeSpent,
        candidates, winner, effect, charge,
        completed, actuationSteps
        >>

Begin ==
    /\ phase = "idle"
    /\ published
    /\ now < Horizon
    /\ beforeRemaining' = remaining
    /\ beforeSpent' = spent
    /\ candidates' =
        IF Fault = "OmitReady"
        THEN ReadyAt(now, remaining) \ {Urgent}
        ELSE ReadyAt(now, remaining)
    /\ winner' = NULL
    /\ effect' = NULL
    /\ charge' = 0
    /\ phase' = "ready"
    /\ UNCHANGED <<
        now, checked, published, remaining, spent,
        completed, actuationSteps
        >>

Select(job) ==
    /\ phase = "ready"
    /\ candidates # {}
    /\ job \in candidates
    /\ IF Fault = "ReverseUrgency"
       THEN \A other \in candidates : Precedes(other, job)
       ELSE \A other \in candidates : Precedes(job, other)
    /\ winner' = job
    /\ phase' = "selected"
    /\ UNCHANGED <<
        now, checked, published,
        remaining, spent, beforeRemaining, beforeSpent,
        candidates, effect, charge,
        completed, actuationSteps
        >>

SelectIdle ==
    /\ phase = "ready"
    /\ candidates = {} \/ Fault = "IdleReady"
    /\ winner' = NULL
    /\ phase' = "selected"
    /\ UNCHANGED <<
        now, checked, published,
        remaining, spent, beforeRemaining, beforeSpent,
        candidates, effect, charge,
        completed, actuationSteps
        >>

QuantumCharge ==
    IF Fault = "SuppressProgress" THEN 0
    ELSE IF Fault = "AccelerateProgress" THEN 2
    ELSE 1

ActuateWork ==
    /\ phase = "selected"
    /\ winner \in Jobs
    /\ QuantumCharge <= beforeRemaining[winner]
    /\ effect' =
        IF Fault = "MisdirectEffect"
        THEN IF winner = Urgent THEN Later ELSE Urgent
        ELSE winner
    /\ charge' = QuantumCharge
    /\ remaining' = [beforeRemaining EXCEPT ![winner] = @ - QuantumCharge]
    /\ spent' = [beforeSpent EXCEPT ![winner] = @ + QuantumCharge]
    /\ actuationSteps' = actuationSteps + 1
    /\ phase' = "actuated"
    /\ UNCHANGED <<
        now, checked, published, beforeRemaining, beforeSpent,
        candidates, winner, completed
        >>

ActuateIdle ==
    /\ phase = "selected"
    /\ winner = NULL
    /\ effect' = NULL
    /\ charge' = 0
    /\ remaining' = beforeRemaining
    /\ spent' = beforeSpent
    /\ actuationSteps' = actuationSteps + 1
    /\ phase' = "actuated"
    /\ UNCHANGED <<
        now, checked, published, beforeRemaining, beforeSpent,
        candidates, winner, completed
        >>

Complete ==
    /\ \/ phase = "actuated"
       \/ /\ Fault = "SkipActuation"
          /\ phase = "selected"
    /\ now < Horizon
    /\ now' = now + 1
    /\ completed' = completed + 1
    /\ phase' = "idle"
    /\ UNCHANGED <<
        checked, published,
        remaining, spent, beforeRemaining, beforeSpent,
        candidates, winner, effect, charge, actuationSteps
        >>

Terminate ==
    /\ phase = "idle"
    /\ now = Horizon
    /\ phase' = "done"
    /\ UNCHANGED <<
        now, checked, published,
        remaining, spent, beforeRemaining, beforeSpent,
        candidates, winner, effect, charge,
        completed, actuationSteps
        >>

Next ==
    \/ \E i \in Intervals : CheckInterval(i)
    \/ Publish
    \/ Begin
    \/ \E job \in Jobs : Select(job)
    \/ SelectIdle
    \/ ActuateWork
    \/ ActuateIdle
    \/ Complete
    \/ Terminate

Spec == Init /\ [][Next]_vars

====
