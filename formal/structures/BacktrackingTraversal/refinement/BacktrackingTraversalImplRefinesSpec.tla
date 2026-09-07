---- MODULE BacktrackingTraversalImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for the executable modulo-three traversal. The  *)
(* visited Vec is projected to a set because visited_unique makes order a  *)
(* hidden representation detail. Tokens map fieldwise. Read guards stutter. *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, Sequences

CONSTANTS BranchFactor, MaxDepth, InitAux
ASSUME BranchFactorType == BranchFactor \in Nat /\ BranchFactor >= 2
ASSUME MaxDepthType == MaxDepth \in Nat /\ MaxDepth >= 1
ASSUME InitAuxType == InitAux \in {0, 1, 2}

AuxSet == {0, 1, 2}
DeltaSet == {1, 2}
MutateImpl(v, d) == (v + d) % 3
UndoImpl(v, d) == (v + (3 - d)) % 3

VARIABLES branch_factor, max_depth, init_aux, path, aux, ledger, visited
vars == <<branch_factor, max_depth, init_aux, path, aux, ledger, visited>>

B == INSTANCE BacktrackingTraversalUndo WITH
        BranchFactor <- BranchFactor,
        MaxDepth <- MaxDepth,
        InitAux <- InitAux,
        AuxDomain <- AuxSet,
        Deltas <- DeltaSet,
        Mutate <- MutateImpl,
        Undo <- UndoImpl,
        path <- path,
        aux <- aux,
        ledger <- ledger,
        visited <- visited

ImplInvariant ==
    /\ branch_factor = BranchFactor
    /\ max_depth = MaxDepth
    /\ init_aux = InitAux
    /\ B!TypeInvariant
    /\ B!Pairing
    /\ B!StateRestoration
    /\ B!RecordedLeafValidity

Init ==
    /\ branch_factor = BranchFactor
    /\ max_depth = MaxDepth
    /\ init_aux = InitAux
    /\ path = <<>>
    /\ aux = InitAux
    /\ ledger = <<>>
    /\ visited = {}
    /\ ImplInvariant

ImplDescend(c, d) ==
    /\ ImplInvariant
    /\ Len(path) < max_depth
    /\ c \in 1..branch_factor
    /\ d \in DeltaSet
    /\ ledger' = Append(ledger, [saved |-> aux, delta |-> d])
    /\ aux' = MutateImpl(aux, d)
    /\ path' = Append(path, c)
    /\ UNCHANGED <<branch_factor, max_depth, init_aux, visited>>
    /\ ImplInvariant'

ImplVisit ==
    /\ ImplInvariant
    /\ Len(path) = max_depth
    /\ path \notin visited
    /\ visited' = visited \cup {path}
    /\ UNCHANGED <<branch_factor, max_depth, init_aux, path, aux, ledger>>
    /\ ImplInvariant'

ImplAscend ==
    /\ ImplInvariant
    /\ Len(path) >= 1
    /\ aux' = UndoImpl(aux, ledger[Len(path)].delta)
    /\ ledger' = SubSeq(ledger, 1, Len(path) - 1)
    /\ path' = SubSeq(path, 1, Len(path) - 1)
    /\ UNCHANGED <<branch_factor, max_depth, init_aux, visited>>
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars
ImplNext ==
    \/ \E c \in 1..BranchFactor, d \in DeltaSet : ImplDescend(c, d)
    \/ ImplVisit
    \/ ImplAscend
    \/ ImplReadOrReject
Spec == Init /\ [][ImplNext]_vars

Refinement == B!Spec
====
