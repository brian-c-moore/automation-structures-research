---- MODULE ReductionStreamFromAuditSink ----
\* Tested construction of ReductionStream from AuditSink. AuditSink's log is
\* the consumed prefix, Hash is instantiated as Op, `result` maps to last_hash,
\* and `pos` maps to Len(log). The refinement follows directly from AuditSink's
\* Record transition: it appends the next source value and updates last_hash
\* with Op(last_hash, value).
\*
\* The construction has no held glue variables; both target variables are
\* projections of component state. It assumes Identity = 0 because AuditSink
\* initializes last_hash to zero, and it inherits the atomicity of Record. The
\* refinement establishes only the ordered left fold; it does not require or
\* transfer an associativity theorem.

EXTENDS Naturals, Sequences

CONSTANTS Src, Op(_, _), Identity

OpImpl(a, b) == a + b
SrcImpl == <<3, 1, 2>>

\* The stream's value set, supplied to the component as its operation domain.
Vals == {Src[i] : i \in 1..Len(Src)}

\* AuditSink component state. No glue variables.
VARIABLES log, last_hash   \* No glue variables: both are component state.

vars == <<log, last_hash>>

\* The kept primitive, with its chain function instantiated to the target's
\* combine. This is the whole content of the reduction: Hash IS Op.
ASink == INSTANCE AuditSink WITH log        <- log,
                                 last_hash  <- last_hash,
                                 Operations <- Vals,
                                 MaxLogLen  <- Len(Src),
                                 Hash       <- Op

\* The kept primitive's own obligations are checked alongside the refinement.
\* They constrain the reachable log, but the refinement proof unfolds Record
\* rather than assuming these invariants as premises.
ChainSafety ==
    /\ ASink!ChainIntegrity
    /\ ASink!HashConsistency
    /\ ASink!HashBindsContent

TypeInvariant == ASink!TypeInvariant

\* --- CF-001 Projections: both target variables are derived ---
ResultView == last_hash
PosView == Len(log)

Init == ASink!Init

\* Consume the next element: the component's own Record, called with the
\* element the stream supplies at the current position. Written through the
\* instance, so the component's operation appears verbatim rather than
\* relabelled (the AllocationSnapshot standard).
CConsume == ASink!Record(Src[Len(log) + 1])

Next == CConsume

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to ReductionStream ---
RS == INSTANCE ReductionStream WITH
        result   <- ResultView,
        pos      <- PosView,
        Src      <- Src,
        Op       <- Op,
        Identity <- Identity

\* The target is AuditSink read through the carry and log-length projections.
ReductionStreamRefinement == RS!Spec
====
