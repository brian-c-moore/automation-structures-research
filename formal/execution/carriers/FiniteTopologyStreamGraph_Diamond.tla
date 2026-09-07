---- MODULE FiniteTopologyStreamGraph_Diamond ----
\* One source, two middle nodes, and one two-input sink exercise atomic
\* fan-out, cyclic selected fan-in, synchronized fan-in, and state edges.
EXTENDS Naturals

NodesDef == {"source", "left", "right", "sink"}
StreamEdgesDef == {"sl", "sr", "lk", "rk"}
StateEdgesDef == {"state-left", "state-right", "state-sink"}
\* The linear profile exercises two payload identities. This profile keeps one
\* payload so its state space is spent on diamond topology and lifecycle seams.
PayloadsDef == {"p1"}
NoEdgeDef == "no-edge"
InitialNodesDef == {"source"}
MaxPublishesDef == 1

StreamSourceDef(e) ==
    CASE e \in {"sl", "sr"} -> "source"
      [] e = "lk" -> "left"
      [] OTHER -> "right"

StreamTargetDef(e) ==
    CASE e = "sl" -> "left"
      [] e = "sr" -> "right"
      [] OTHER -> "sink"

StateSourceDef(e) ==
    CASE e \in {"state-left", "state-right"} -> "source"
      [] OTHER -> "left"

StateTargetDef(e) ==
    CASE e = "state-left" -> "left"
      [] e = "state-right" -> "right"
      [] OTHER -> "sink"

CapacityDef(e) == 2

EdgeOrderDef(e) ==
    CASE e = "sl" -> 1
      [] e = "sr" -> 2
      [] e = "lk" -> 3
      [] OTHER -> 4

VARIABLES
    queues, sent, received, discarded, published, edge_status, cursor,
    reached, selection_valid

INSTANCE FiniteTopologyStreamGraph WITH
    Nodes <- NodesDef,
    StreamEdges <- StreamEdgesDef,
    StateEdges <- StateEdgesDef,
    Payloads <- PayloadsDef,
    NoEdge <- NoEdgeDef,
    InitialNodes <- InitialNodesDef,
    MaxPublishes <- MaxPublishesDef,
    StreamSource <- StreamSourceDef,
    StreamTarget <- StreamTargetDef,
    StateSource <- StateSourceDef,
    StateTarget <- StateTargetDef,
    Capacity <- CapacityDef,
    EdgeOrder <- EdgeOrderDef,
    queues <- queues,
    sent <- sent,
    received <- received,
    discarded <- discarded,
    published <- published,
    edge_status <- edge_status,
    cursor <- cursor,
    reached <- reached,
    selection_valid <- selection_valid
====
