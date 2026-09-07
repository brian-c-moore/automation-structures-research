---- MODULE BacktrackingTraversalUndoFromRegistry_NEG ----
\* Negative control for checkpoint fidelity. CDescend registers InitAux
\* instead of the current AuxView. Registry invariants and the first descent
\* remain valid, but a second descent cannot simulate the target Descend action
\* and must violate BacktrackingTraversalUndoRefinement.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS BranchFactor, MaxDepth, InitAux, AuxDomain, Deltas,
          Mutate(_, _), Undo(_, _)

MutateImpl(v, d) == (v + d) % 3
UndoImpl(v, d)   == (v + (3 - d)) % 3

Token == [saved : AuxDomain, delta : Deltas]

VARIABLES reg_entries, c_path, c_visited

vars == <<reg_entries, c_path, c_visited>>

Reg == INSTANCE ResourceRegistry WITH entries <- reg_entries,
                                      Keys    <- 1..MaxDepth,
                                      Values  <- Token

ComponentSafety == Reg!UniqueMapping

TypeInvariant ==
    /\ Reg!TypeInvariant
    /\ c_path \in Seq(1..BranchFactor)
    /\ c_visited \subseteq Seq(1..BranchFactor)

DefaultToken == [saved |-> InitAux, delta |-> CHOOSE d \in Deltas : TRUE]

TokenView(i) ==
    IF \E t \in Token : <<i, t>> \in reg_entries
    THEN CHOOSE t \in Token : <<i, t>> \in reg_entries
    ELSE DefaultToken

LedgerView == [i \in 1..Len(c_path) |-> TokenView(i)]

AuxView ==
    IF Len(c_path) = 0
    THEN InitAux
    ELSE Mutate(TokenView(Len(c_path)).saved, TokenView(Len(c_path)).delta)

Init ==
    /\ Reg!Init
    /\ c_path    = <<>>
    /\ c_visited = {}

\* Fault: the checkpoint records InitAux rather than the current AuxView.
CDescend(c, d) ==
    /\ Len(c_path) # MaxDepth
    /\ c \in 1..BranchFactor
    /\ d \in Deltas
    /\ Reg!Register(Len(c_path) + 1, [saved |-> InitAux, delta |-> d])
    /\ c_path' = Append(c_path, c)
    /\ UNCHANGED c_visited

CVisit ==
    /\ Len(c_path) = MaxDepth
    /\ c_path \notin c_visited
    /\ c_visited' = c_visited \cup {c_path}
    /\ UNCHANGED <<reg_entries, c_path>>

CAscend ==
    /\ Len(c_path) >= 1
    /\ Reg!Deregister(Len(c_path))
    /\ c_path' = SubSeq(c_path, 1, Len(c_path) - 1)
    /\ UNCHANGED c_visited

Next ==
    \/ \E c \in 1..BranchFactor, d \in Deltas : CDescend(c, d)
    \/ CVisit
    \/ CAscend

Spec == Init /\ [][Next]_vars

BTU == INSTANCE BacktrackingTraversalUndo WITH
        path         <- c_path,
        aux          <- AuxView,
        ledger       <- LedgerView,
        visited      <- c_visited,
        BranchFactor <- BranchFactor,
        MaxDepth     <- MaxDepth,
        InitAux      <- InitAux,
        AuxDomain    <- AuxDomain,
        Deltas       <- Deltas,
        Mutate       <- Mutate,
        Undo         <- Undo

BacktrackingTraversalUndoRefinement == BTU!Spec
====
