------------------- MODULE BacktrackingTraversalDecomposed ------------------
(* Decomposition of the backtracking-traversal algorithmic primitive.

   Canonical BacktrackingTraversal maintains Pairing == (aux = InitAux + Depth)
   because its Descend action appends a branch to `path` (raising Depth) AND
   increments `aux` (the descent mutation) in one ATOMIC step.  This
   decomposition splits Descend's apply+push from the descent bookkeeping: a
   separate ExtendPath (append to `path`, push the saved aux) then ApplyMutation
   (increment `aux`).  Between the two steps Depth has grown but the descent
   mutation has not yet been applied, so aux = InitAux + Depth - 1 and the
   canonical Pairing is violated.

   Targets the primitive's ACTUAL .cfg invariant `Pairing`.  TLC finds Pairing
   violated at the intermediate "descending" state.                            *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS BranchFactor, MaxDepth, InitAux

VARIABLES path, aux, aux_stack, visited, pc

vars == <<path, aux, aux_stack, visited, pc>>

Depth == Len(path)
IsLeaf == Depth = MaxDepth

\* Canonical invariant: aux tracks depth exactly (each descent +1, each ascent -1).
Pairing ==
    aux = InitAux + Depth

Init ==
    /\ path = <<>>
    /\ aux = InitAux
    /\ aux_stack = <<>>
    /\ visited = {}
    /\ pc = "ready"

\* Step 1 of the split Descend: extend the path (Depth grows) and push the saved
\* aux, WITHOUT applying the descent mutation.  The canonical Descend does both
\* (push+append AND aux+1) in one step.
ExtendPath(c) ==
    /\ pc = "ready"
    /\ ~IsLeaf
    /\ c \in 1..BranchFactor
    /\ aux_stack' = Append(aux_stack, aux)
    /\ path' = Append(path, c)
    /\ pc' = "descending"
    /\ UNCHANGED <<aux, visited>>

\* Step 2 of the split Descend: apply the deferred descent mutation, restoring
\* Pairing.
ApplyMutation ==
    /\ pc = "descending"
    /\ aux' = aux + 1
    /\ pc' = "ready"
    /\ UNCHANGED <<path, aux_stack, visited>>

\* Visit and Ascend are unchanged from the canonical machine (only Descend is
\* decomposed); both fire only from a fully-descended "ready" state.
Visit ==
    /\ pc = "ready"
    /\ IsLeaf
    /\ path \notin visited
    /\ visited' = visited \cup {path}
    /\ UNCHANGED <<path, aux, aux_stack, pc>>

Ascend ==
    /\ pc = "ready"
    /\ Depth >= 1
    /\ LET saved == aux_stack[Depth]
       IN  /\ aux' = saved
           /\ aux_stack' = SubSeq(aux_stack, 1, Depth - 1)
           /\ path' = SubSeq(path, 1, Depth - 1)
    /\ UNCHANGED <<visited, pc>>

Next ==
    \/ \E c \in 1..BranchFactor : ExtendPath(c)
    \/ ApplyMutation
    \/ Visit
    \/ Ascend

Spec == Init /\ [][Next]_vars
=============================================================================
