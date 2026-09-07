---- MODULE ReductionImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for the incremental additive Reducer. processed *)
(* and remaining partition the immutable ghost original sequence. pos is   *)
(* the derived Len(processed) observation used by the canonical machine.    *)
(* done and the standalone batch folds do not mutate this carrier.          *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, Sequences

CONSTANT Source
ASSUME SourceType == Source \in Seq(Nat)
Add(a, b) == a + b
ConfiguredSource == <<3, 1, 2>>

VARIABLES original, processed, remaining, result, pos
vars == <<original, processed, remaining, result, pos>>

R == INSTANCE ReductionStream WITH
        Src <- Source,
        Op <- Add,
        Identity <- 0,
        result <- result,
        pos <- pos

Partition == processed \o remaining = original
ImplInvariant ==
    /\ original = Source
    /\ processed \in Seq(Nat)
    /\ remaining \in Seq(Nat)
    /\ Partition
    /\ pos = Len(processed)
    /\ R!TypeInvariant
    /\ R!ConsumedPrefixFold

Init ==
    /\ original = Source
    /\ processed = <<>>
    /\ remaining = Source
    /\ result = 0
    /\ pos = 0
    /\ ImplInvariant

ImplProcess ==
    /\ ImplInvariant
    /\ Len(remaining) > 0
    /\ pos < Len(Source)
    /\ processed' = Append(processed, Head(remaining))
    /\ remaining' = Tail(remaining)
    \* Partition and pos = Len(processed) identify this with Head(remaining).
    /\ result' = result + Source[pos + 1]
    /\ pos' = pos + 1
    /\ UNCHANGED original
    /\ ImplInvariant'

ImplReadOrDone == UNCHANGED vars
ImplNext == ImplProcess \/ ImplReadOrDone
Spec == Init /\ [][ImplNext]_vars

Refinement == R!Spec
====
