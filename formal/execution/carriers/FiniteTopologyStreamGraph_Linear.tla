---- MODULE FiniteTopologyStreamGraph_Linear ----
\* Four-node linear instance used to compare the general carrier with the
\* accepted finite StreamGraph chain profile.
EXTENDS Naturals

NodesDef == {"n1", "n2", "n3", "n4"}
StreamEdgesDef == {"e12", "e23", "e34"}
StateEdgesDef == {"s12", "s23", "s34"}
PayloadsDef == {"p1", "p2"}
NoEdgeDef == "no-edge"
InitialNodesDef == {"n1"}
MaxPublishesDef == 1

StreamSourceDef(e) ==
    CASE e = "e12" -> "n1"
      [] e = "e23" -> "n2"
      [] OTHER -> "n3"

StreamTargetDef(e) ==
    CASE e = "e12" -> "n2"
      [] e = "e23" -> "n3"
      [] OTHER -> "n4"

StateSourceDef(e) ==
    CASE e = "s12" -> "n1"
      [] e = "s23" -> "n2"
      [] OTHER -> "n3"

StateTargetDef(e) ==
    CASE e = "s12" -> "n2"
      [] e = "s23" -> "n3"
      [] OTHER -> "n4"

CapacityDef(e) == 2

EdgeOrderDef(e) ==
    CASE e = "e12" -> 1
      [] e = "e23" -> 2
      [] OTHER -> 3

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
