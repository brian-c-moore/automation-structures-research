---- MODULE DepthDerivedBacktrackingFromGlue ----
(* Pure-connective construction for the depth-derived target.

   Held state contains a path cursor and accumulated recorded leaves. The
   target auxiliary value and restoration stack are projections of path depth.
   A successful refinement therefore establishes a property of the weak target
   model: its restoration state is derivable rather than independently held. *)
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
    /\ Depth >= 1
    /\ path' = SubSeq(path, 1, Depth - 1)
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
