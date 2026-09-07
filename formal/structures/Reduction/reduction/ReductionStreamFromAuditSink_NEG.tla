---- MODULE ReductionStreamFromAuditSink_NEG ----
\* Negative control for ReductionStreamFromAuditSink: one deliberately broken
\* step, proving the refinement check is non-vacuous.
\*
\* Fault injection: the record's hash is computed from the identity instead of
\* the running carry -- `Op(Identity, op)` in place of `Op(last_hash, op)`.
\* That is precisely the chaining, and nothing else changes: the append, the
\* length bound, the entry shape and the mapping are verbatim.
\*
\* This mutates the transition clause used by the refinement proof. Cut the
\* link to the predecessor and the carry becomes a function of the last
\* element only, so it is no longer the fold of the consumed prefix.
\*
\* REQUIRED OUTCOME: VIOLATED. If this control PASSED, the chain would not be
\* what supplies ConsumedPrefixFold and the reduction would be unsupported.
\*
\* This mutation also breaks the component's ChainIntegrity. That is a second
\* expected consequence, not evidence that ChainIntegrity is assumed by the
\* refinement proof; the proof unfolds the unmutated Record transition.

EXTENDS Naturals, Sequences

CONSTANTS Src, Op(_, _), Identity

OpImpl(a, b) == a + b
SrcImpl == <<3, 1, 2>>

Vals == {Src[i] : i \in 1..Len(Src)}

VARIABLES log, last_hash

vars == <<log, last_hash>>

ASink == INSTANCE AuditSink WITH log        <- log,
                                 last_hash  <- last_hash,
                                 Operations <- Vals,
                                 MaxLogLen  <- Len(Src),
                                 Hash       <- Op

ChainSafety ==
    /\ ASink!ChainIntegrity
    /\ ASink!HashConsistency
    /\ ASink!HashBindsContent

TypeInvariant == ASink!TypeInvariant

ResultView == last_hash
PosView == Len(log)

Init == ASink!Init

\* Fault injection: the carry is dropped from the hash computation.
CConsume ==
    /\ Len(log) < Len(Src)
    /\ LET op == Src[Len(log) + 1]
           new_hash == Op(Identity, op)
           entry == [operation |-> op, prev_hash |-> last_hash, hash |-> new_hash]
       IN /\ log' = Append(log, entry)
          /\ last_hash' = new_hash

Next == CConsume

Spec == Init /\ [][Next]_vars

RS == INSTANCE ReductionStream WITH
        result   <- ResultView,
        pos      <- PosView,
        Src      <- Src,
        Op       <- Op,
        Identity <- Identity

ReductionStreamRefinement == RS!Spec
====
