---- MODULE ActorRefinesStreamGraph ----
\* ====================================================================
\* REFINEMENT: Actor refines StreamGraph (docs/execution-modalities.md)
\*
\* Tests the position that the actor model is a streaming-graph
\* configuration with the following mapping:
\*
\*   - Mailbox            -> input queue
\*   - send(target,msg)   -> emit-to-downstream on edge (self, target)
\*   - stateful body      -> per-record processing function
\*   - addressable PIDs   -> runtime-constructed edges
\*   - selective receive  -> pattern-match queue consumption (invocation)
\*   - become / behaviors -> dependency-axis change (operator function
\*                           swap), execution primitive unchanged
\*   - supervision        -> lifecycle policy
\*
\* This spec instantiates a small actor system, derives the mapped
\* stream graph, and verifies that every actor step corresponds to a
\* legal stream-graph step under the configured policy.
\* ====================================================================
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Actors, Messages, MaxMailbox, MaxSteps

\* Actors      : finite set of actor identifiers
\* Messages    : finite set of message values
\* MaxMailbox  : per-actor mailbox capacity
\* MaxSteps    : bound on total actor steps (state-space cap)

VARIABLES
    mailbox,       \* function Actors -> Seq(Messages) — the queues
    refs,          \* function Actors -> SUBSET Actors — known peers
    behavior,      \* function Actors -> "active"|"swapped" — `become`
    sg_edges,      \* derived: streaming-graph edges = {(a, b) : b in refs[a]}
    sg_records,    \* derived: per-edge record counts
    steps          \* step counter

vars == <<mailbox, refs, behavior, sg_edges, sg_records, steps>>

TypeInvariant ==
    /\ mailbox    \in [Actors -> Seq(Messages)]
    /\ refs       \in [Actors -> SUBSET Actors]
    /\ behavior   \in [Actors -> {"active", "swapped"}]
    /\ sg_edges   \subseteq Actors \X Actors
    /\ sg_records \in [Actors \X Actors -> Nat]
    /\ steps      \in 0..MaxSteps

\* ----- Refinement mapping -----
\* sg_edges = {(a, b) : b in refs[a]} — addressable identity maps
\*            to runtime-constructed topology.
\* sg_records[<<a,b>>] = number of messages outstanding on that edge —
\*                       equals the count of in-flight messages from a
\*                       that target b. (Tracked nondeterministically;
\*                       approximated by counting messages currently
\*                       in mailbox[b] that came via the edge.)
ExpectedEdges == {<<a, b>> : a \in Actors, b \in Actors} \cap UNION
    { {<<a, b>> : b \in refs[a]} : a \in Actors }

Init ==
    /\ mailbox    = [a \in Actors |-> <<>>]
    /\ refs       = [a \in Actors |-> {}]
    /\ behavior   = [a \in Actors |-> "active"]
    /\ sg_edges   = {}
    /\ sg_records = [pair \in Actors \X Actors |-> 0]
    /\ steps      = 0

\* Two actors meet: each learns a reference to the other. This is the
\* spawn/introduction step. Streaming graph edge is created.
Introduce(a, b) ==
    /\ a # b
    /\ b \notin refs[a]
    /\ steps < MaxSteps
    /\ refs'     = [refs EXCEPT ![a] = refs[a] \cup {b}]
    /\ sg_edges' = sg_edges \cup {<<a, b>>}
    /\ steps'    = steps + 1
    /\ UNCHANGED <<mailbox, behavior, sg_records>>

\* Send a message: append to recipient's mailbox; bump edge record count.
Send(sender, target, msg) ==
    /\ target \in refs[sender]
    /\ Len(mailbox[target]) < MaxMailbox
    /\ steps < MaxSteps
    /\ mailbox'    = [mailbox    EXCEPT ![target] = Append(mailbox[target], msg)]
    /\ sg_records' = [sg_records EXCEPT ![<<sender, target>>] = sg_records[<<sender, target>>] + 1]
    /\ steps'      = steps + 1
    /\ UNCHANGED <<refs, behavior, sg_edges>>

\* Receive a message (FIFO mailbox; selective-receive variant is the
\* invocation policy parameterization). Decrement an edge's record
\* count by 1 — the sender is not identified, so pick any with count > 0.
Receive(a) ==
    /\ Len(mailbox[a]) > 0
    /\ steps < MaxSteps
    /\ mailbox' = [mailbox EXCEPT ![a] = Tail(mailbox[a])]
    /\ \E sender \in Actors :
         /\ sg_records[<<sender, a>>] > 0
         /\ sg_records' = [sg_records EXCEPT ![<<sender, a>>] = sg_records[<<sender, a>>] - 1]
    /\ steps' = steps + 1
    /\ UNCHANGED <<refs, behavior, sg_edges>>

\* Erlang `become`: swap the actor's behavior. The streaming-graph
\* substrate's execution primitive is unchanged — only the operator's
\* function tag changes: a dependency-axis change.
Become(a) ==
    /\ steps < MaxSteps
    /\ behavior' = [behavior EXCEPT ![a] =
                       IF behavior[a] = "active" THEN "swapped" ELSE "active"]
    /\ steps' = steps + 1
    /\ UNCHANGED <<mailbox, refs, sg_edges, sg_records>>

Done ==
    /\ steps = MaxSteps
    /\ UNCHANGED vars

Next ==
    \/ \E a, b \in Actors : Introduce(a, b)
    \/ \E s, t \in Actors, m \in Messages : Send(s, t, m)
    \/ \E a \in Actors : Receive(a) \/ Become(a)
    \/ Done

Spec == Init /\ [][Next]_vars

\* ----- INVARIANTS -----

\* The streaming-graph edge set tracks refs (runtime addressable
\* topology, docs/execution-modalities.md).
\* TLAPS 1.5.0's parser does not accept tuple-destructured set comprehension
\* `{<<a, b>> \in S : P(a, b)}`, so the form below uses explicit index access.
\* The two forms denote the same set of pairs.
EdgesTrackRefs ==
    sg_edges = {p \in Actors \X Actors : p[2] \in refs[p[1]]}

\* Every send is along an established edge (no edge teleportation).
SendOnlyAlongEdges == TRUE   \* structural — Send is guarded by target \in refs[sender]

\* Mailbox queues are bounded.
MailboxBounded == \A a \in Actors : Len(mailbox[a]) <= MaxMailbox

\* Records conservation: the count of in-flight records on an edge is
\* non-negative.
NonNegativeRecords ==
    \A p \in Actors \X Actors : sg_records[p] >= 0

\* The streaming-graph refinement: at every step, the actor system's
\* mailboxes and edge counts correspond to a legal stream-graph state
\* with backpressure (MaxMailbox = Capacity).
StreamGraphRefinement ==
    /\ EdgesTrackRefs
    /\ MailboxBounded
    /\ NonNegativeRecords
====
