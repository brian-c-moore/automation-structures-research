---- MODULE Queues ----
\* ====================================================================
\* SHARED PRIMITIVE: BOUNDED QUEUE WITH BACKPRESSURE
\*
\* A bounded queue whose full state signals backpressure upstream,
\* parameterized by Capacity, written as a shared module.
\*
\* No module under Execution Modalities extends or instantiates this
\* one: StreamGraph defines its own IsFull and IsEmpty, and
\* InvocationPolicies its own QueueBounded and QueueTyped.
\* ====================================================================
EXTENDS Naturals, Sequences

CONSTANTS Capacity, RecordSet
\* Capacity : positive natural - max queue length
\* RecordSet : finite set of record values

EmptyQueue == <<>>

IsEmpty(q) == Len(q) = 0
IsFull(q)  == Len(q) >= Capacity

Enqueue(q, r) == IF IsFull(q) THEN q ELSE Append(q, r)
Dequeue(q)    == IF IsEmpty(q) THEN q ELSE Tail(q)
Peek(q)       == IF IsEmpty(q) THEN CHOOSE r \in RecordSet : TRUE ELSE Head(q)

\* Backpressure flag: derived state. An upstream operator must not push
\* into a full queue. This is enforced at the calling site.
Backpressure(q) == IsFull(q)

\* INVARIANT: queue never exceeds capacity.
QueueBounded(q) == Len(q) <= Capacity

\* INVARIANT: every record in the queue is a member of RecordSet.
QueueTyped(q) == \A i \in 1..Len(q) : q[i] \in RecordSet
====
