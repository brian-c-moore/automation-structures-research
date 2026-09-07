---- MODULE FiniteTopologyStreamGraph ----
\* General finite-topology streaming carrier. Each stream connection owns a
\* bounded FIFO sequence and exact sent, received, and terminal-discard
\* histories. Publication is atomic across every outgoing connection of the
\* selected node. State edges have a separate transition projection.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,
    StreamEdges,
    StateEdges,
    Payloads,
    NoEdge,
    InitialNodes,
    MaxPublishes,
    StreamSource(_),
    StreamTarget(_),
    StateSource(_),
    StateTarget(_),
    Capacity(_),
    EdgeOrder(_)

EdgeCount == Cardinality(StreamEdges)

ASSUME NodesFinite == IsFiniteSet(Nodes)
ASSUME NodesNonEmpty == Nodes # {}
ASSUME StreamEdgesFinite == IsFiniteSet(StreamEdges)
ASSUME StreamEdgesNonEmpty == StreamEdges # {}
ASSUME StateEdgesFinite == IsFiniteSet(StateEdges)
ASSUME EdgeKindsDisjoint == StateEdges \cap StreamEdges = {}
ASSUME PayloadsNonEmpty == Payloads # {}
ASSUME NoEdgeFresh == NoEdge \notin StreamEdges
ASSUME InitialNodesType == InitialNodes \subseteq Nodes
ASSUME MaxPublishesType == MaxPublishes \in Nat \ {0}
ASSUME StreamEndpointsType ==
    \A e \in StreamEdges :
        /\ StreamSource(e) \in Nodes
        /\ StreamTarget(e) \in Nodes
ASSUME StateEndpointsType ==
    \A e \in StateEdges :
        /\ StateSource(e) \in Nodes
        /\ StateTarget(e) \in Nodes
ASSUME CapacityType ==
    \A e \in StreamEdges : Capacity(e) \in Nat \ {0}
ASSUME EdgeOrderType ==
    \A e \in StreamEdges : EdgeOrder(e) \in 1..EdgeCount
ASSUME EdgeOrderUnique ==
    \A e1, e2 \in StreamEdges :
        EdgeOrder(e1) = EdgeOrder(e2) => e1 = e2

OpenStatus == "open"
ClosingStatus == "closing"
ClosedStatus == "closed"
CancelledStatus == "cancelled"
FailedStatus == "failed"

EdgeStatuses ==
    {OpenStatus, ClosingStatus, ClosedStatus, CancelledStatus, FailedStatus}

VARIABLES
    queues,
    sent,
    received,
    discarded,
    published,
    edge_status,
    cursor,
    reached,
    selection_valid

vars ==
    <<queues, sent, received, discarded, published, edge_status, cursor,
      reached, selection_valid>>

StreamProjection ==
    <<queues, sent, received, discarded, published, edge_status, cursor,
      selection_valid>>

StateProjection == reached

Outgoing(n) == {e \in StreamEdges : StreamSource(e) = n}
Incoming(n) == {e \in StreamEdges : StreamTarget(e) = n}
ReadyInputs(n) == {e \in Incoming(n) : Len(queues[e]) > 0}

CyclicRank(position, origin) ==
    ((position + EdgeCount - origin) % EdgeCount) + 1

IsFirstReady(n, e) ==
    /\ e \in ReadyInputs(n)
    /\ \A other \in ReadyInputs(n) :
        CyclicRank(EdgeOrder(e), cursor[n])
            <= CyclicRank(EdgeOrder(other), cursor[n])

NextCursor(e) ==
    IF EdgeOrder(e) = EdgeCount THEN 1 ELSE EdgeOrder(e) + 1

Drained(e) == queues[e] = <<>>
TerminalEdge(e) ==
    edge_status[e] \in {ClosedStatus, CancelledStatus, FailedStatus}

AllTerminal == \A e \in StreamEdges : TerminalEdge(e)

TypeInvariant ==
    /\ queues \in [StreamEdges -> Seq(Payloads)]
    /\ sent \in [StreamEdges -> Seq(Payloads)]
    /\ received \in [StreamEdges -> Seq(Payloads)]
    /\ discarded \in [StreamEdges -> Seq(Payloads)]
    /\ published \in [Nodes -> Seq(Payloads)]
    /\ edge_status \in [StreamEdges -> EdgeStatuses]
    /\ cursor \in [Nodes -> 1..EdgeCount]
    /\ reached \subseteq Nodes
    /\ selection_valid \in BOOLEAN

CapacityBound ==
    \A e \in StreamEdges : Len(queues[e]) <= Capacity(e)

\* Identity and FIFO order are preserved per connection. Terminal discard is
\* explicit, so cancellation and failure cannot erase an outstanding item.
EdgeConservation ==
    \A e \in StreamEdges :
        sent[e] = received[e] \o discarded[e] \o queues[e]

\* Every publication at a node creates exactly one ordered copy on every
\* outgoing connection. This is the multiplicity-aware fan-out statement.
FanoutConservation ==
    \A e \in StreamEdges : sent[e] = published[StreamSource(e)]

TerminalConsistency ==
    \A e \in StreamEdges :
        /\ edge_status[e] \in {OpenStatus, ClosingStatus} => discarded[e] = <<>>
        /\ edge_status[e] = ClosedStatus =>
            /\ Drained(e)
            /\ discarded[e] = <<>>
        /\ edge_status[e] \in {CancelledStatus, FailedStatus} => Drained(e)

SelectedInputExact == selection_valid

Init ==
    /\ queues = [e \in StreamEdges |-> <<>>]
    /\ sent = [e \in StreamEdges |-> <<>>]
    /\ received = [e \in StreamEdges |-> <<>>]
    /\ discarded = [e \in StreamEdges |-> <<>>]
    /\ published = [n \in Nodes |-> <<>>]
    /\ edge_status = [e \in StreamEdges |-> OpenStatus]
    /\ cursor = [n \in Nodes |-> 1]
    /\ reached = InitialNodes
    /\ selection_valid = TRUE

PublishEnabled(n) ==
    /\ n \in Nodes
    /\ Outgoing(n) # {}
    /\ Len(published[n]) < MaxPublishes
    /\ \A e \in Outgoing(n) :
        /\ edge_status[e] = OpenStatus
        /\ Len(queues[e]) < Capacity(e)

Publish(n, payload) ==
    /\ PublishEnabled(n)
    /\ payload \in Payloads
    /\ queues' =
        [e \in StreamEdges |->
            IF e \in Outgoing(n) THEN Append(queues[e], payload)
            ELSE queues[e]]
    /\ sent' =
        [e \in StreamEdges |->
            IF e \in Outgoing(n) THEN Append(sent[e], payload)
            ELSE sent[e]]
    /\ published' =
        [published EXCEPT ![n] = Append(@, payload)]
    /\ UNCHANGED
        <<received, discarded, edge_status, cursor, reached, selection_valid>>

ReceiveSelected(n, e) ==
    /\ n \in Nodes
    /\ IsFirstReady(n, e)
    /\ queues' = [queues EXCEPT ![e] = Tail(@)]
    /\ received' =
        [received EXCEPT ![e] = Append(@, Head(queues[e]))]
    /\ cursor' = [cursor EXCEPT ![n] = NextCursor(e)]
    /\ selection_valid' = selection_valid /\ IsFirstReady(n, e)
    /\ UNCHANGED
        <<sent, discarded, published, edge_status, reached>>

SynchronizedReady(n) ==
    /\ n \in Nodes
    /\ Incoming(n) # {}
    /\ \A e \in Incoming(n) : Len(queues[e]) > 0

ReceiveSynchronized(n) ==
    /\ SynchronizedReady(n)
    /\ queues' =
        [e \in StreamEdges |->
            IF e \in Incoming(n) THEN Tail(queues[e]) ELSE queues[e]]
    /\ received' =
        [e \in StreamEdges |->
            IF e \in Incoming(n)
            THEN Append(received[e], Head(queues[e]))
            ELSE received[e]]
    /\ UNCHANGED
        <<sent, discarded, published, edge_status, cursor, reached,
          selection_valid>>

RequestClose(e) ==
    /\ e \in StreamEdges
    /\ edge_status[e] = OpenStatus
    /\ edge_status' =
        [edge_status EXCEPT
            ![e] = IF Drained(e) THEN ClosedStatus ELSE ClosingStatus]
    /\ UNCHANGED
        <<queues, sent, received, discarded, published, cursor, reached,
          selection_valid>>

FinalizeClose(e) ==
    /\ e \in StreamEdges
    /\ edge_status[e] = ClosingStatus
    /\ Drained(e)
    /\ edge_status' = [edge_status EXCEPT ![e] = ClosedStatus]
    /\ UNCHANGED
        <<queues, sent, received, discarded, published, cursor, reached,
          selection_valid>>

Terminate(e, outcome) ==
    /\ e \in StreamEdges
    /\ edge_status[e] \in {OpenStatus, ClosingStatus}
    /\ outcome \in {CancelledStatus, FailedStatus}
    /\ queues' = [queues EXCEPT ![e] = <<>>]
    /\ discarded' = [discarded EXCEPT ![e] = @ \o queues[e]]
    /\ edge_status' = [edge_status EXCEPT ![e] = outcome]
    /\ UNCHANGED
        <<sent, received, published, cursor, reached, selection_valid>>

Cancel(e) == Terminate(e, CancelledStatus)

Fail(e) == Terminate(e, FailedStatus)

AdvanceState(e) ==
    /\ e \in StateEdges
    /\ StateSource(e) \in reached
    /\ StateTarget(e) \notin reached
    /\ reached' = reached \cup {StateTarget(e)}
    /\ UNCHANGED StreamProjection

StreamStep ==
    \/ \E n \in Nodes, payload \in Payloads : Publish(n, payload)
    \/ \E n \in Nodes, e \in StreamEdges : ReceiveSelected(n, e)
    \/ \E n \in Nodes : ReceiveSynchronized(n)
    \/ \E e \in StreamEdges : RequestClose(e)
    \/ \E e \in StreamEdges : FinalizeClose(e)
    \/ \E e \in StreamEdges : Cancel(e)
    \/ \E e \in StreamEdges : Fail(e)

StateStep == \E e \in StateEdges : AdvanceState(e)

Next == StreamStep \/ StateStep

Spec == Init /\ [][Next]_vars

RejectedPublish(n, payload) ==
    /\ n \in Nodes
    /\ payload \in Payloads
    /\ ~PublishEnabled(n)
    /\ UNCHANGED vars

RejectedSelectedReceive(n) ==
    /\ n \in Nodes
    /\ ReadyInputs(n) = {}
    /\ UNCHANGED vars
====
