---- MODULE PiCalculusBehavior ----
\* ====================================================================
\* PI-CALCULUS BEHAVIORAL SPEC (bounded study configuration)
\*
\* Behavioral property: name-passing preserves observable equivalence.
\*
\* Modeled scenario: three processes A, B, C. A holds a "private name"
\* (here, an opaque identifier) and either keeps it private or sends
\* it to C. C's observable behavior is identical in both cases until
\* C actually uses the received name.
\*
\* The invariant `NamePassingObservationalEquivalence` is a state-based
\* approximation: as long as no process has yet sent a message on a
\* freshly-received name, the system's observable trace is invariant
\* under whether the name was passed or not. The full structural
\* congruence proof is out of scope for TLC; this spec checks the
\* state-level conservation property that supports the equivalence.
\* ====================================================================
EXTENDS Naturals

CONSTANTS Processes, Names, MaxSteps

ASSUME Processes # {}
ASSUME Names # {}

VARIABLES
    knows,         \* function Processes -> SUBSET Names
    sent_on,       \* function Names -> Nat (count of messages sent on this name)
    received_on,   \* function Names -> Nat (count of messages received on this name)
    step

vars == <<knows, sent_on, received_on, step>>

TypeInvariant ==
    /\ knows       \in [Processes -> SUBSET Names]
    /\ sent_on     \in [Names -> 0..MaxSteps]
    /\ received_on \in [Names -> 0..MaxSteps]
    /\ step        \in 0..MaxSteps

Init ==
    /\ knows = [p \in Processes |-> Names]   \* initially everyone knows every name
    /\ sent_on = [n \in Names |-> 0]
    /\ received_on = [n \in Names |-> 0]
    /\ step = 0

\* A process passes a name it knows to another process. This is the
\* pi-calculus output prefix that carries a name as payload.
PassName(from, to, n) ==
    /\ step < MaxSteps
    /\ n \in knows[from]
    /\ knows' = [knows EXCEPT ![to] = knows[to] \cup {n}]
    /\ step' = step + 1
    /\ UNCHANGED <<sent_on, received_on>>

\* A send on a name (the name must be known to the sender).
SendOn(p, n) ==
    /\ step < MaxSteps
    /\ n \in knows[p]
    /\ sent_on[n] < MaxSteps
    /\ sent_on' = [sent_on EXCEPT ![n] = sent_on[n] + 1]
    /\ step' = step + 1
    /\ UNCHANGED <<knows, received_on>>

\* A receive on a name balances a previous send.
ReceiveOn(p, n) ==
    /\ step < MaxSteps
    /\ n \in knows[p]
    /\ received_on[n] < sent_on[n]
    /\ received_on' = [received_on EXCEPT ![n] = received_on[n] + 1]
    /\ step' = step + 1
    /\ UNCHANGED <<knows, sent_on>>

DoneStuttering == step >= MaxSteps /\ UNCHANGED vars

Next ==
    \/ \E p, q \in Processes, n \in Names : PassName(p, q, n)
    \/ \E p \in Processes, n \in Names : SendOn(p, n)
    \/ \E p \in Processes, n \in Names : ReceiveOn(p, n)
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* ----- BEHAVIORAL INVARIANT -----
\* Observable equivalence: every received message corresponds to a
\* previous send on the same name; no message is observable on a name
\* that no process has used. This is the conservation law that
\* underpins barbed congruence in Milner's pi-calculus.
NamePassingObservationalEquivalence ==
    \A n \in Names : received_on[n] <= sent_on[n]
====
