---- MODULE BacktrackingTraversalUndo ----
(* Paired do/undo traversal with explicit restoration state.

   A descent applies a domain-supplied delta and records the prior auxiliary
   value plus that delta. An ascent applies the recorded inverse and removes
   the token. Auxiliary state is therefore held state rather than a function
   of path depth.

   Obligations:
     O1 Pairing          -- one token exists per outstanding descent, and the
                            current auxiliary value is the head mutation.
     O2 StateRestoration -- token saved values form a chain from InitAux.
     O3 RecordedLeafValidity -- every recorded visit is a valid full-depth
                               path.

   Pairing and StateRestoration are independently falsifiable: splitting path
   extension from mutation breaks Pairing, while saving a value other than the
   current auxiliary state breaks StateRestoration. Full leaf coverage,
   scheduling order, and graph-search completeness are not claimed.

   Mutate and Undo are domain parameters. The proof assumes closure and the
   round-trip law; the TLC configuration supplies addition and subtraction
   modulo three as one finite instance.                                      *)
EXTENDS Naturals, Sequences

CONSTANTS
    BranchFactor,   \* number of children per non-leaf node (>= 2)
    MaxDepth,       \* depth of the decision tree (root = depth 0)
    InitAux,        \* initial value of the auxiliary state
    AuxDomain,      \* the values the auxiliary state ranges over
    Deltas,         \* the domain-supplied mutations available at a descent
    Mutate(_, _),   \* apply a delta to an aux value (the DO)
    Undo(_, _)      \* apply the delta's inverse (the UNDO)

\* Concrete realization for TLC (cfg: Mutate <- MutateImpl, Undo <- UndoImpl):
\* addition modulo 3, the smallest group with two distinct non-identity
\* elements. AuxDomain = {0,1,2} and Deltas = {1,2} in the .cfg.
MutateImpl(v, d) == (v + d) % 3
UndoImpl(v, d)   == (v + (3 - d)) % 3

VARIABLES
    path,       \* sequence of branch choices on current descent (length = depth)
    aux,        \* current auxiliary state value (mutated on descent)
    ledger,     \* stack of UNDO TOKENS, one per outstanding descent
    visited     \* set of complete paths (leaf nodes reached)

vars == <<path, aux, ledger, visited>>

\* ---- Helpers --------------------------------------------------------------

Depth == Len(path)

IsLeaf == Depth = MaxDepth

\* The undo token: what the aux state was before the descent, and which
\* mutation was applied. This held value is the restoration checkpoint.
Token == [saved : AuxDomain, delta : Deltas]

\* ---- Type invariant -------------------------------------------------------

TypeInvariant ==
    /\ path \in Seq(1..BranchFactor)
    /\ Len(path) <= MaxDepth
    /\ aux \in AuxDomain
    /\ ledger \in Seq(Token)
    /\ visited \subseteq Seq(1..BranchFactor)

\* ---- Safety invariants ----------------------------------------------------

\* O1 Pairing: every do on the current path is recorded and applied exactly
\* once. One ledger entry exists per outstanding descent, and the current aux
\* is the head entry's mutation applied to the head entry's saved value.
Pairing ==
    /\ Len(ledger) = Depth
    /\ Depth = 0 => aux = InitAux
    /\ Depth > 0 => aux = Mutate(ledger[Depth].saved, ledger[Depth].delta)

\* O2 StateRestoration: the checkpoint ledger is a well-formed chain -- the
\* first entry restores to InitAux, and each later entry's saved value is its
\* predecessor's value with the predecessor's delta applied.  This is what
\* makes an ascent from any depth land on the value that depth was entered
\* with, and it is not derivable from `path`: the deltas are free.
StateRestoration ==
    /\ Len(ledger) >= 1 => ledger[1].saved = InitAux
    /\ \A i \in 2..Len(ledger) :
           ledger[i].saved = Mutate(ledger[i-1].saved, ledger[i-1].delta)

\* O3 RecordedLeafValidity: every entry in the visited set is a full-depth leaf path
\* with valid branches.
\* Full coverage of all leaves is liveness of an exhaustive scheduler, not a
\* safety property of this order-parametric model.
RecordedLeafValidity ==
    \A p \in visited :
        /\ Len(p) = MaxDepth
        /\ \A i \in 1..MaxDepth : p[i] \in 1..BranchFactor

\* Compatibility alias only. This formula does not establish leaf coverage or
\* general traversal completeness.
Completeness == RecordedLeafValidity

\* ---- Init -----------------------------------------------------------------

Init ==
    /\ path    = <<>>           \* start at the root
    /\ aux     = InitAux        \* initial auxiliary state
    /\ ledger  = <<>>           \* no outstanding descents at the root
    /\ visited = {}

\* ---- Actions --------------------------------------------------------------

\* Descend pushes the undo token, applies the mutation, and extends the path in
\* one transition.
Descend(c, d) ==
    /\ ~IsLeaf
    /\ c \in 1..BranchFactor
    /\ d \in Deltas
    /\ LET token == [saved |-> aux, delta |-> d]
       IN  /\ ledger' = Append(ledger, token)
           /\ aux'    = Mutate(token.saved, token.delta)
    /\ path' = Append(path, c)
    /\ UNCHANGED visited

\* Visit (at a leaf): record the current path as visited.
Visit ==
    /\ IsLeaf
    /\ path \notin visited
    /\ visited' = visited \cup {path}
    /\ UNCHANGED <<path, aux, ledger>>

\* Ascend applies the recorded inverse and pops the head token. Under O1 and
\* O2, aux' equals that token's saved value.
Ascend ==
    /\ Depth >= 1
    /\ aux'    = Undo(aux, ledger[Depth].delta)
    /\ ledger' = SubSeq(ledger, 1, Depth - 1)
    /\ path'   = SubSeq(path, 1, Depth - 1)
    /\ UNCHANGED visited

Next ==
    \/ \E c \in 1..BranchFactor, d \in Deltas : Descend(c, d)
    \/ Visit
    \/ Ascend

Spec == Init /\ [][Next]_vars

\* BacktrackingTraversalUndo_Proof proves the four public invariants under the
\* mutation closure and round-trip premises.
====
