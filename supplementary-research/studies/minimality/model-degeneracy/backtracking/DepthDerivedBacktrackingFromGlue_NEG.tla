---- MODULE DepthDerivedBacktrackingFromGlue_NEG ----
(* Correspondence-breaking control for the pure-connective construction.

   AscendC removes two path levels in one step. The construction remains typed,
   but the mapped auxiliary value drops by two and matches no target action.
   The Refinement property is expected to fail at the supplied bounds.       *)
EXTENDS Naturals, Sequences

CONSTANTS BranchFactor, MaxDepth, InitAux

VARIABLES path, visited

vars == <<path, visited>>

Depth == Len(path)

TypeInvariant ==
    /\ path \in Seq(1..BranchFactor)
    /\ Len(path) <= MaxDepth
    /\ visited \subseteq Seq(1..BranchFactor)

Init ==
    /\ path = <<>>
    /\ visited = {}

DescendC(c) ==
    /\ Depth < MaxDepth
    /\ c \in 1..BranchFactor
    /\ path' = Append(path, c)
    /\ UNCHANGED visited

VisitC ==
    /\ Depth = MaxDepth
    /\ path \notin visited
    /\ visited' = visited \cup {path}
    /\ UNCHANGED path

AscendC ==
    /\ Depth >= 2
    /\ path' = SubSeq(path, 1, Depth - 2)
    /\ UNCHANGED visited

Next ==
    \/ \E c \in 1..BranchFactor : DescendC(c)
    \/ VisitC
    \/ AscendC

Spec == Init /\ [][Next]_vars

MapAux == InitAux + Depth
MapAuxStack == [i \in 1..Depth |-> InitAux + (i - 1)]

Target == INSTANCE DepthDerivedBacktracking WITH
    path <- path,
    aux <- MapAux,
    aux_stack <- MapAuxStack,
    visited <- visited,
    BranchFactor <- BranchFactor,
    MaxDepth <- MaxDepth,
    InitAux <- InitAux

Refinement == Target!Spec
====
