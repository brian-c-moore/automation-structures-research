---- MODULE BacktrackingTraversalUndo_NEG_Pairing ----
\* Negative control for Pairing. Ascend pops the path and ledger without
\* applying the recorded inverse, so the isolated configuration must reach a
\* state whose auxiliary value does not match the remaining head token.

EXTENDS Naturals, Sequences

CONSTANTS
    BranchFactor,
    MaxDepth,
    InitAux,
    AuxDomain,
    Deltas,
    Mutate(_, _),
    Undo(_, _)

MutateImpl(v, d) == (v + d) % 3
UndoImpl(v, d)   == (v + (3 - d)) % 3

VARIABLES
    path,
    aux,
    ledger,
    visited

vars == <<path, aux, ledger, visited>>

Depth == Len(path)

IsLeaf == Depth = MaxDepth

Token == [saved : AuxDomain, delta : Deltas]

TypeInvariant ==
    /\ path \in Seq(1..BranchFactor)
    /\ Len(path) <= MaxDepth
    /\ aux \in AuxDomain
    /\ ledger \in Seq(Token)
    /\ visited \subseteq Seq(1..BranchFactor)

Pairing ==
    /\ Len(ledger) = Depth
    /\ Depth = 0 => aux = InitAux
    /\ Depth > 0 => aux = Mutate(ledger[Depth].saved, ledger[Depth].delta)

StateRestoration ==
    /\ Len(ledger) >= 1 => ledger[1].saved = InitAux
    /\ \A i \in 2..Len(ledger) :
           ledger[i].saved = Mutate(ledger[i-1].saved, ledger[i-1].delta)

RecordedLeafValidity ==
    \A p \in visited :
        /\ Len(p) = MaxDepth
        /\ \A i \in 1..MaxDepth : p[i] \in 1..BranchFactor

Completeness == RecordedLeafValidity

Init ==
    /\ path    = <<>>
    /\ aux     = InitAux
    /\ ledger  = <<>>
    /\ visited = {}

Descend(c, d) ==
    /\ ~IsLeaf
    /\ c \in 1..BranchFactor
    /\ d \in Deltas
    /\ LET token == [saved |-> aux, delta |-> d]
       IN  /\ ledger' = Append(ledger, token)
           /\ aux'    = Mutate(token.saved, token.delta)
    /\ path' = Append(path, c)
    /\ UNCHANGED visited

Visit ==
    /\ IsLeaf
    /\ path \notin visited
    /\ visited' = visited \cup {path}
    /\ UNCHANGED <<path, aux, ledger>>

Ascend ==
    /\ Depth >= 1
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ aux'    = aux   \* fault: the recorded inverse is never applied
\* ---- MUTATION ENDS.
    /\ ledger' = SubSeq(ledger, 1, Depth - 1)
    /\ path'   = SubSeq(path, 1, Depth - 1)
    /\ UNCHANGED visited

Next ==
    \/ \E c \in 1..BranchFactor, d \in Deltas : Descend(c, d)
    \/ Visit
    \/ Ascend

Spec == Init /\ [][Next]_vars

====
