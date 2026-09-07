---- MODULE InvocationPolicies ----
\* ====================================================================
\* POLICY SPEC: INVOCATION (docs/execution-modalities.md)
\*
\* Queue consumption strategy. FIFO, priority, pattern-match
\* (Erlang selective receive), age-weighted.
\*
\* Priorities and Pattern are hardcoded for the sample model because
\* TLC's .cfg parser does not accept record-literal CONSTANTS.
\* ====================================================================
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxQueue, MaxAge

\* Items are integers 1..3.
Items      == {1, 2, 3}
Pattern    == {1, 3}
Priorities == [it \in Items |-> CASE it = 1 -> 2 [] it = 2 -> 1 [] it = 3 -> 3]

VARIABLES queue, ages, served

vars == <<queue, ages, served>>

TypeInvariant ==
    /\ queue  \in Seq(Items)
    /\ ages   \in [Items -> 0..MaxAge]
    /\ served \in 0..(2 * MaxQueue)

\* ----- POLICY: FIFO -----
FifoIndex(q) == 1

\* ----- POLICY: PRIORITY -----
PriorityIndex(q) ==
    IF Len(q) = 0 THEN 0
    ELSE CHOOSE i \in 1..Len(q) :
            \A j \in 1..Len(q) : Priorities[q[i]] >= Priorities[q[j]]

\* ----- POLICY: PATTERN-MATCH -----
PatternIndex(q) ==
    IF \E i \in 1..Len(q) : q[i] \in Pattern
    THEN CHOOSE i \in 1..Len(q) :
            /\ q[i] \in Pattern
            /\ \A j \in 1..(i-1) : q[j] \notin Pattern
    ELSE 0

\* ----- POLICY: AGE-WEIGHTED -----
AgeWeightedIndex(q) ==
    IF Len(q) = 0 THEN 0
    ELSE CHOOSE i \in 1..Len(q) :
            \A j \in 1..Len(q) : ages[q[i]] >= ages[q[j]]

Init ==
    /\ queue  = <<>>
    /\ ages   = [it \in Items |-> 0]
    /\ served = 0

Enqueue(it) ==
    /\ Len(queue) < MaxQueue
    /\ served < 2 * MaxQueue
    /\ \E a \in 0..MaxAge :
        /\ ages' = [ages EXCEPT ![it] = a]
        /\ queue' = Append(queue, it)
    /\ UNCHANGED served

DequeueFifo ==
    /\ Len(queue) > 0
    /\ served < 2 * MaxQueue
    /\ queue'  = Tail(queue)
    /\ served' = served + 1
    /\ UNCHANGED ages

DequeuePriority ==
    /\ Len(queue) > 0
    /\ served < 2 * MaxQueue
    /\ LET i == PriorityIndex(queue) IN
         queue' = SubSeq(queue, 1, i-1) \o SubSeq(queue, i+1, Len(queue))
    /\ served' = served + 1
    /\ UNCHANGED ages

DequeuePattern ==
    /\ Len(queue) > 0
    /\ PatternIndex(queue) # 0
    /\ served < 2 * MaxQueue
    /\ LET i == PatternIndex(queue) IN
         queue' = SubSeq(queue, 1, i-1) \o SubSeq(queue, i+1, Len(queue))
    /\ served' = served + 1
    /\ UNCHANGED ages

DequeueAge ==
    /\ Len(queue) > 0
    /\ served < 2 * MaxQueue
    /\ LET i == AgeWeightedIndex(queue) IN
         queue' = SubSeq(queue, 1, i-1) \o SubSeq(queue, i+1, Len(queue))
    /\ served' = served + 1
    /\ UNCHANGED ages

Next ==
    \/ \E it \in Items : Enqueue(it)
    \/ DequeueFifo
    \/ DequeuePriority
    \/ DequeuePattern
    \/ DequeueAge
    \/ ((Len(queue) = 0 \/ served >= 2 * MaxQueue) /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

QueueBounded == Len(queue) <= MaxQueue
QueueTyped == \A i \in 1..Len(queue) : queue[i] \in Items
====
