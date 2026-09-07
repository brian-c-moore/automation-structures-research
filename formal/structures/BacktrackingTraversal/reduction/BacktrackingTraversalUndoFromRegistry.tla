---- MODULE BacktrackingTraversalUndoFromRegistry ----
\* Construction of BacktrackingTraversalUndo from ResourceRegistry and G v1.1.
\* Registry keys are depths and values are undo tokens. Register performs the
\* descent push/upsert; Deregister performs the ascent pop.
\*
\* The target obligations are Pairing (one token per outstanding descent with
\* aux equal to the head mutation) and StateRestoration (a token chain from
\* InitAux). `c_path` is CF-002 Cursor glue and `c_visited` is CF-003
\* Accumulator glue; target ledger and auxiliary views are projections of the
\* registry store.
\*
\* AuditSink supplies an append-only chain and cannot implement the required
\* pop action, so it does not cover the full action surface. This construction
\* assumes atomic fused registry/path transitions and the target's domain
\* premise that Undo is the inverse of Mutate. The refinement establishes only
\* the mapped finite behavior under those premises.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS BranchFactor, MaxDepth, InitAux, AuxDomain, Deltas,
          Mutate(_, _), Undo(_, _)

MutateImpl(v, d) == (v + d) % 3
UndoImpl(v, d)   == (v + (3 - d)) % 3

\* The undo token, exactly the target's.
Token == [saved : AuxDomain, delta : Deltas]

VARIABLES reg_entries,   \* ResourceRegistry<1..MaxDepth -> Token> (component)
          c_path,        \* CF-002 Cursor  (glue)
          c_visited      \* CF-003 Accumulator (glue)

vars == <<reg_entries, c_path, c_visited>>

\* --- The kept component, written through its own instance -----------------
Reg == INSTANCE ResourceRegistry WITH entries <- reg_entries,
                                      Keys    <- 1..MaxDepth,
                                      Values  <- Token

\* ResourceRegistry's UniqueMapping obligation over the token store.
ComponentSafety == Reg!UniqueMapping

TypeInvariant ==
    /\ Reg!TypeInvariant
    /\ c_path \in Seq(1..BranchFactor)
    /\ c_visited \subseteq Seq(1..BranchFactor)

\* --- CF-001 Projections: both obligation-carrying target values are derived -

\* A defaulted registry view (the EquivalenceClass / ActuationPass pattern).
\* The construction only ever reads keys 1..Len(c_path), all of which are
\* registered, so the default branch is unreachable; it is present for
\* totality.
DefaultToken == [saved |-> InitAux, delta |-> CHOOSE d \in Deltas : TRUE]

TokenView(i) ==
    IF \E t \in Token : <<i, t>> \in reg_entries
    THEN CHOOSE t \in Token : <<i, t>> \in reg_entries
    ELSE DefaultToken

\* The ledger is the registry read out along the current path.
LedgerView == [i \in 1..Len(c_path) |-> TokenView(i)]

\* AuxView is the mutation recorded by the head token, making Pairing's value
\* clause a projection of registry state.
AuxView ==
    IF Len(c_path) = 0
    THEN InitAux
    ELSE Mutate(TokenView(Len(c_path)).saved, TokenView(Len(c_path)).delta)

Init ==
    /\ Reg!Init
    /\ c_path    = <<>>
    /\ c_visited = {}

\* Descend registers the undo token at the new depth and advances the cursor.
CDescend(c, d) ==
    /\ Len(c_path) # MaxDepth
    /\ c \in 1..BranchFactor
    /\ d \in Deltas
    /\ Reg!Register(Len(c_path) + 1, [saved |-> AuxView, delta |-> d])
    /\ c_path' = Append(c_path, c)
    /\ UNCHANGED c_visited

CVisit ==
    /\ Len(c_path) = MaxDepth
    /\ c_path \notin c_visited
    /\ c_visited' = c_visited \cup {c_path}
    /\ UNCHANGED <<reg_entries, c_path>>

\* Ascend: deregister the head token and retract the cursor. Deregister is
\* the component operation the append-only carrier cannot offer.
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

\* --- Refinement mapping to BacktrackingTraversalUndo ----------------------
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

\* The target obligations restated over the construction state.
MappedPairing ==
    /\ Len(LedgerView) = Len(c_path)
    /\ Len(c_path) = 0 => AuxView = InitAux
    /\ Len(c_path) > 0 =>
           AuxView = Mutate(LedgerView[Len(c_path)].saved,
                            LedgerView[Len(c_path)].delta)

MappedStateRestoration ==
    /\ Len(LedgerView) >= 1 => LedgerView[1].saved = InitAux
    /\ \A i \in 2..Len(LedgerView) :
           LedgerView[i].saved = Mutate(LedgerView[i-1].saved,
                                        LedgerView[i-1].delta)

MappedCompleteness ==
    \A p \in c_visited :
        /\ Len(p) = MaxDepth
        /\ \A i \in 1..MaxDepth : p[i] \in 1..BranchFactor

BacktrackingTraversalUndoRefinement == BTU!Spec
====
