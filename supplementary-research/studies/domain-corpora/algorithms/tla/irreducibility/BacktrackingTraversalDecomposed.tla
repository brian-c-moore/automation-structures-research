---- MODULE BacktrackingTraversalDecomposed ----
(*
  Models the decomposition of BacktrackingTraversal into:
    TraversalEngine   — drives descent and ascent steps
    ActuationPass     — applies the descent mutation at each node
    InverseActuationPass — applies the ascent inverse at each node

  The paired-undo is an EXTERNAL CONVENTION between ActuationPass and
  InverseActuationPass, not an invariant local to any single primitive.
  Each primitive's own invariant holds throughout; only the composition-level
  Pairing property can be broken.

  The governance gap: in the decomposed model, each of the three primitives
  operates independently.  TraversalEngine can fire an Ascend step without
  InverseActuationPass having fired the corresponding inverse.  Similarly,
  the ActuationPass may fire a descent mutation, and then TraversalEngine
  ascends WITHOUT triggering InverseActuationPass first.

  There is no individual-primitive invariant that catches this:
  - TraversalEngine only requires that it walks the tree (path and visited)
  - ActuationPass only requires that it applies mutations when requested
  - InverseActuationPass only requires that it applies inverses when requested

  The Pairing invariant — every descent mutation applied has a matching
  inverse before any sibling subtree is entered — is spread across the
  three primitives and can be broken in the decomposed model.

  Expected VIOLATION of: Pairing
  (a reachable state where aux /= InitAux + Depth, with no individual
   primitive's own invariant violated)

  BacktrackingTraversal is confirmed as a primitive: no decomposition of
  it preserves Pairing.
*)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    BranchFactor,   \* number of children per non-leaf node
    MaxDepth,       \* depth of the decision tree
    InitAux         \* initial auxiliary state

VARIABLES
    path,         \* current path in the tree (TraversalEngine state)
    aux,          \* auxiliary state (ActuationPass/InverseActuationPass target)
    visited,      \* set of visited leaf paths (TraversalEngine state)
    \* Per-primitive flags: track whether the actuation step has fired
    \* for the current descent, without enforcing that the inverse fires
    \* before ascent.
    descent_applied  \* TRUE if ActuationPass has fired for the current depth

vars == <<path, aux, visited, descent_applied>>

Depth == Len(path)
IsLeaf == Depth = MaxDepth

\* ---- Individual-primitive invariants (all must hold throughout) ------------

\* TraversalEngine invariant: path is a valid partial path.
TraversalInvariant ==
    /\ path \in Seq(1..BranchFactor)
    /\ Len(path) <= MaxDepth
    /\ visited \subseteq Seq(1..BranchFactor)

\* ActuationPass invariant: aux >= InitAux (mutations only increment).
ActuationInvariant ==
    aux >= InitAux

\* InverseActuationPass invariant: aux <= InitAux + MaxDepth (bounded above).
InverseActuationInvariant ==
    aux <= InitAux + MaxDepth

\* ---- Composition-level invariant (the governance property lost) -----------

\* Pairing: at every reachable state, aux = InitAux + Depth.
\* This is the paired-undo property: each descent increments aux by 1 and
\* each ascent decrements by 1.  In the primitive, this is enforced atomically.
\* In the decomposed model, ascent can fire before the inverse actuation,
\* leaving aux > InitAux + Depth.
Pairing ==
    aux = InitAux + Depth

\* ---- Init -----------------------------------------------------------------

Init ==
    /\ path           = <<>>
    /\ aux            = InitAux
    /\ visited        = {}
    /\ descent_applied = FALSE

\* ---- TraversalEngine: Descend step ----------------------------------------
\* TraversalEngine drives the descent.  It does NOT apply the mutation itself.
\* It sets descent_applied = FALSE to signal that ActuationPass should fire.

TEDescend(c) ==
    /\ ~IsLeaf
    /\ c \in 1..BranchFactor
    /\ path'           = Append(path, c)
    /\ descent_applied' = FALSE     \* mutation not yet applied for this depth
    /\ UNCHANGED <<aux, visited>>

\* ---- ActuationPass: apply descent mutation --------------------------------
\* Increments aux (the descent mutation).

APApplyDescent ==
    /\ ~descent_applied
    /\ aux'            = aux + 1
    /\ descent_applied' = TRUE
    /\ UNCHANGED <<path, visited>>

\* ---- TraversalEngine: Visit a leaf ----------------------------------------

TEVisit ==
    /\ IsLeaf
    /\ path \notin visited
    /\ visited' = visited \cup {path}
    /\ UNCHANGED <<path, aux, descent_applied>>

\* ---- TraversalEngine: Ascend step -----------------------------------------
\* THE GOVERNANCE GAP: TraversalEngine can ascend WITHOUT InverseActuationPass
\* having fired.  The pairing is an external convention; nothing in any single
\* primitive's invariant enforces it.

TEAscend ==
    /\ Depth >= 1
    /\ path' = SubSeq(path, 1, Depth - 1)
    /\ UNCHANGED <<aux, visited, descent_applied>>

\* ---- InverseActuationPass: apply ascent inverse ---------------------------
\* Decrements aux (the inverse mutation).  This is SEPARATE from TEAscend.
\* In the decomposed model, it may never fire if the convention is not
\* upheld — or it may fire after TEAscend has already changed Depth.

IAPApplyAscent ==
    /\ aux > InitAux
    /\ aux' = aux - 1
    /\ UNCHANGED <<path, visited, descent_applied>>

\* ---- Next -----------------------------------------------------------------
\* All three primitives' steps are interleaved freely.  The convention that
\* IAPApplyAscent fires before TEAscend is NOT enforced at the primitive
\* level — it is an external agreement between components.

Next ==
    \/ \E c \in 1..BranchFactor : TEDescend(c)
    \/ APApplyDescent
    \/ TEVisit
    \/ TEAscend
    \/ IAPApplyAscent

Spec == Init /\ [][Next]_vars
=============================================================================
