------------------ MODULE BacktrackingTraversalUndoDecomposed ----------------
(* Irreducibility-by-construction for the concept-faithful
   BacktrackingTraversalUndo.

   This is the corpus's existing BacktrackingTraversal decomposition, run
   against the enriched model.  It witnesses that the paired do/undo is a
   primitive-boundary property rather than a constituent invariant, and it is
   this entry's atomicity evidence.

   The split is the same one BacktrackingTraversalDecomposed makes: the
   canonical Descend pushes the undo token AND applies the descent mutation
   in one atomic step; here ExtendPath pushes the token and extends the path,
   and ApplyMutation applies the deferred mutation afterwards.  Between the
   two steps the ledger has grown but the mutation has not been applied, so
   `aux` is stale against the head entry and Pairing is violated.

   Difference from the pinned instrument: against the pinned model the
   violation is aux = InitAux + Depth - 1, an off-by-one in a derived
   quantity, the pinned Pairing recomputing aux from the path length so that
   the whole ledger is a projection of `path`.  Here the violated equation
   relates two pieces of held state -- the live aux and the head token's
   recorded saved/delta -- and the deltas are chosen freely, so neither side
   is recomputable from the position.

   The split is arranged so that O2 (StateRestoration, the ledger's chain
   law) still holds at the intermediate state: the pushed token records the
   pre-mutation aux, which is what the chain requires.  The two obligations
   therefore fail independently: TLC violates Pairing here while
   StateRestoration is untouched.

   TLC must find a violation of Pairing.                                    *)
EXTENDS Naturals, Sequences

CONSTANTS BranchFactor, MaxDepth, InitAux, AuxDomain, Deltas,
          Mutate(_, _), Undo(_, _)

MutateImpl(v, d) == (v + d) % 3
UndoImpl(v, d)   == (v + (3 - d)) % 3

VARIABLES path, aux, ledger, visited, pc

vars == <<path, aux, ledger, visited, pc>>

Depth == Len(path)
IsLeaf == Depth = MaxDepth

Token == [saved : AuxDomain, delta : Deltas]

TypeInvariant ==
    /\ path \in Seq(1..BranchFactor)
    /\ Len(path) <= MaxDepth
    /\ aux \in AuxDomain
    /\ ledger \in Seq(Token)
    /\ visited \subseteq Seq(1..BranchFactor)
    /\ pc \in {"ready", "descending"}

\* The base module's O1, verbatim.
Pairing ==
    /\ Len(ledger) = Depth
    /\ Depth = 0 => aux = InitAux
    /\ Depth > 0 => aux = Mutate(ledger[Depth].saved, ledger[Depth].delta)

\* The base module's O2, verbatim.  It SURVIVES the split; that is the
\* independence check.
StateRestoration ==
    /\ Len(ledger) >= 1 => ledger[1].saved = InitAux
    /\ \A i \in 2..Len(ledger) :
           ledger[i].saved = Mutate(ledger[i-1].saved, ledger[i-1].delta)

\* The base module's O3, Completeness, is NOT carried here, and the omission is
\* deliberate: it constrains only the paths recorded in `visited`; Visit is
\* carried over (guarded to fire from "ready"); and neither half of the split
\* touches `visited` -- ExtendPath and ApplyMutation both leave it UNCHANGED.
\* The defusion cannot reach that obligation, so it is neither defined nor
\* checked in this model.

Init ==
    /\ path    = <<>>
    /\ aux     = InitAux
    /\ ledger  = <<>>
    /\ visited = {}
    /\ pc      = "ready"

\* Step 1 of the split Descend: push the undo token and extend the path,
\* WITHOUT applying the descent mutation.  The canonical Descend does both in
\* one step.
ExtendPath(c, d) ==
    /\ pc = "ready"
    /\ ~IsLeaf
    /\ c \in 1..BranchFactor
    /\ d \in Deltas
    /\ ledger' = Append(ledger, [saved |-> aux, delta |-> d])
    /\ path'   = Append(path, c)
    /\ pc'     = "descending"
    /\ UNCHANGED <<aux, visited>>

\* Step 2 of the split Descend: apply the deferred mutation, restoring
\* Pairing.
ApplyMutation ==
    /\ pc = "descending"
    /\ LET token == ledger[Len(ledger)]
       IN  aux' = Mutate(token.saved, token.delta)
    /\ pc' = "ready"
    /\ UNCHANGED <<path, ledger, visited>>

\* Visit and Ascend are unchanged from the canonical machine (only Descend is
\* decomposed); both fire only from a fully-descended "ready" state.
Visit ==
    /\ pc = "ready"
    /\ IsLeaf
    /\ path \notin visited
    /\ visited' = visited \cup {path}
    /\ UNCHANGED <<path, aux, ledger, pc>>

Ascend ==
    /\ pc = "ready"
    /\ Depth >= 1
    /\ aux'    = Undo(aux, ledger[Depth].delta)
    /\ ledger' = SubSeq(ledger, 1, Depth - 1)
    /\ path'   = SubSeq(path, 1, Depth - 1)
    /\ UNCHANGED <<visited, pc>>

Next ==
    \/ \E c \in 1..BranchFactor, d \in Deltas : ExtendPath(c, d)
    \/ ApplyMutation
    \/ Visit
    \/ Ascend

Spec == Init /\ [][Next]_vars
=============================================================================
