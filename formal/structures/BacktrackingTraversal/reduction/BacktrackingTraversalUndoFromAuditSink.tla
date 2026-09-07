---- MODULE BacktrackingTraversalUndoFromAuditSink ----
\* Partial construction of BacktrackingTraversalUndo from AuditSink. With
\* Hash instantiated as Mutate, HashConsistency supplies the current auxiliary
\* carry, HashBindsContent supplies the token shape, and ChainIntegrity supplies
\* the saved-value recurrence.
\*
\* AuditSink provides only the append action Record. A backtracking ledger also
\* requires an ascent that removes the head token, so this construction has no
\* Ascend action and refines only by exposing fewer target behaviors. It cannot
\* return to a sibling subtree and is not a full-action-surface reduction.
\*
\* c_path is CF-002 Cursor glue and c_visited is CF-003 Accumulator glue; aux
\* and ledger are CF-001 projections of AuditSink state. Because AuditSink
\* initializes last_hash to zero, the mapping requires InitAux = 0.
EXTENDS Naturals, Sequences

CONSTANTS BranchFactor, MaxDepth, InitAux, AuxDomain, Deltas,
          Mutate(_, _), Undo(_, _)

MutateImpl(v, d) == (v + d) % 3
UndoImpl(v, d)   == (v + (3 - d)) % 3

VARIABLES log, last_hash,   \* AuditSink component state
          c_path,           \* CF-002 Cursor (glue)
          c_visited         \* CF-003 Accumulator (glue)

vars == <<log, last_hash, c_path, c_visited>>

\* AuditSink with its chain function instantiated as the target mutation.
ASink == INSTANCE AuditSink WITH log        <- log,
                                 last_hash  <- last_hash,
                                 Operations <- Deltas,
                                 MaxLogLen  <- MaxDepth,
                                 Hash       <- Mutate

\* AuditSink's three chain obligations under the Mutate substitution.
ComponentSafety ==
    /\ ASink!ChainIntegrity
    /\ ASink!HashConsistency
    /\ ASink!HashBindsContent

TypeInvariant ==
    /\ ASink!TypeInvariant
    /\ c_path \in Seq(1..BranchFactor)
    /\ c_visited \subseteq Seq(1..BranchFactor)

\* --- CF-001 Projections ---------------------------------------------------
\* Each audit record projects to the saved value and delta of one undo token.
LedgerView ==
    [i \in 1..Len(log) |-> [saved |-> log[i].prev_hash,
                            delta |-> log[i].operation]]

AuxView == last_hash

Init ==
    /\ ASink!Init
    /\ c_path    = <<>>
    /\ c_visited = {}

\* Descend: the component's own Record, called with the chosen delta.
CDescend(c, d) ==
    /\ Len(c_path) # MaxDepth
    /\ c \in 1..BranchFactor
    /\ d \in Deltas
    /\ ASink!Record(d)
    /\ c_path' = Append(c_path, c)
    /\ UNCHANGED c_visited

CVisit ==
    /\ Len(c_path) = MaxDepth
    /\ c_path \notin c_visited
    /\ c_visited' = c_visited \cup {c_path}
    /\ UNCHANGED <<log, last_hash, c_path>>

\* AuditSink has no action that shrinks the log, so the construction has no
\* CAscend transition and exposes only a strict subset of target behaviors.

Next ==
    \/ \E c \in 1..BranchFactor, d \in Deltas : CDescend(c, d)
    \/ CVisit

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

\* The target obligations over the construction state. StateRestoration and
\* the value clause of Pairing use only AuditSink state; the token-count clause
\* of Pairing also depends on the cursor.
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

BacktrackingTraversalUndoRefinement == BTU!Spec
====
