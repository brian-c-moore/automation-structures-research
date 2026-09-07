---- MODULE DepthDerivedBacktracking ----
(* Depth-derived paired traversal used only for a model-adequacy experiment.

   This target models the auxiliary value and restoration stack as arithmetic
   functions of path depth. It proves a paired depth discipline and valid
   recorded leaves. It does not model arbitrary domain mutations or a held
   checkpoint ledger. The current BacktrackingTraversal structure uses the
   stronger arbitrary-mutation target in the active corpus.                 *)
EXTENDS Naturals, Sequences

CONSTANTS
    BranchFactor,
    MaxDepth,
    InitAux

VARIABLES
    path,
    aux,
    aux_stack,
    visited

vars == <<path, aux, aux_stack, visited>>

Depth == Len(path)
IsLeaf == Depth = MaxDepth

TypeInvariant ==
    /\ path \in Seq(1..BranchFactor)
    /\ Len(path) <= MaxDepth
    /\ aux \in Nat
    /\ aux_stack \in Seq(Nat)
    /\ Len(aux_stack) = Depth
    /\ visited \subseteq Seq(1..BranchFactor)

(* The auxiliary value is determined entirely by path depth. *)
DepthCoupling == aux = InitAux + Depth

(* Every saved value is likewise determined by its stack position. *)
DerivedStack ==
    \A i \in 1..Depth : aux_stack[i] = InitAux + (i - 1)

(* Every recorded visit is a well-formed full-depth path. This is a safety
   property about recorded entries, not eventual coverage of all leaves. *)
RecordedLeavesValid ==
    \A p \in visited :
        /\ Len(p) = MaxDepth
        /\ \A i \in 1..MaxDepth : p[i] \in 1..BranchFactor

Init ==
    /\ path = <<>>
    /\ aux = InitAux
    /\ aux_stack = <<>>
    /\ visited = {}

Descend(c) ==
    /\ ~IsLeaf
    /\ c \in 1..BranchFactor
    /\ aux_stack' = Append(aux_stack, aux)
    /\ path' = Append(path, c)
    /\ aux' = aux + 1
    /\ UNCHANGED visited

Visit ==
    /\ IsLeaf
    /\ path \notin visited
    /\ visited' = visited \cup {path}
    /\ UNCHANGED <<path, aux, aux_stack>>

Ascend ==
    /\ Depth >= 1
    /\ aux' = aux_stack[Depth]
    /\ aux_stack' = SubSeq(aux_stack, 1, Depth - 1)
    /\ path' = SubSeq(path, 1, Depth - 1)
    /\ UNCHANGED visited

Next ==
    \/ \E c \in 1..BranchFactor : Descend(c)
    \/ Visit
    \/ Ascend

Spec == Init /\ [][Next]_vars
====
