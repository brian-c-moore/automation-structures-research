---- MODULE StmPremiseBinding ----
\* Safety model for the global-epoch STM premises used by FEX-DOM-TXN-01.
\* Published transactional-memory and opacity results remain source
\* authorities. This model checks the construction side for a finite two-cell,
\* one-writer, one-reader history above one atomic epoch word.

EXTENDS Naturals, FiniteSets

CONSTANTS Cells, X, Y, Transactions, Writer, Reader, NULL, Fault

Faults == {
    "None",
    "ReuseIdentity",
    "UndeclaredRead",
    "IgnoreEpochValidation",
    "StaleAcquire",
    "MisdirectWrite",
    "EarlyPublish",
    "AbortAfterWrite",
    "SkipPublication"
}

ASSUME ModelTypes ==
    /\ Cells = {X, Y}
    /\ X # Y
    /\ Transactions = {Writer, Reader}
    /\ Writer # Reader
    /\ NULL \notin Cells \cup Transactions \cup Nat
    /\ Fault \in Faults

VARIABLES
    epoch, heap,
    registry, readerDeclaration, writerDeclaration,
    writerStatus, writerStart, acquiredFrom, publishedEpoch,
    readerStatus, readerStart, readerRead, readerValues,
    applied, actualEffects, advanced

vars == <<
    epoch, heap,
    registry, readerDeclaration, writerDeclaration,
    writerStatus, writerStart, acquiredFrom, publishedEpoch,
    readerStatus, readerStart, readerRead, readerValues,
    applied, actualEffects, advanced
>>

Even(value) == value % 2 = 0

TypeInvariant ==
    /\ epoch \in 0..4
    /\ heap \in [Cells -> 0..1]
    /\ registry \subseteq Transactions
    /\ readerDeclaration \subseteq Cells
    /\ writerDeclaration \subseteq Cells
    /\ writerStatus \in {"new", "active", "acquired", "published", "committed", "aborted"}
    /\ writerStart \in 0..4
    /\ acquiredFrom \in 0..4
    /\ publishedEpoch \in 0..4
    /\ readerStatus \in {"new", "active", "committed", "aborted"}
    /\ readerStart \in 0..4
    /\ readerRead \subseteq Cells
    /\ readerValues \in [Cells -> {NULL, 0, 1}]
    /\ applied \subseteq Cells
    /\ actualEffects \in [Cells -> Cells \cup {NULL}]
    /\ advanced \in BOOLEAN

IdentityBinding ==
    /\ (writerStatus # "new" => Writer \in registry)
    /\ (readerStatus # "new" => Reader \in registry)

AccessBinding ==
    /\ readerRead \subseteq readerDeclaration
    /\ applied \subseteq writerDeclaration

AcquisitionBinding ==
    writerStatus \in {"acquired", "published", "committed"} =>
        /\ Even(acquiredFrom)
        /\ acquiredFrom = writerStart

OddEpochExclusion ==
    writerStatus = "acquired" => ~Even(epoch)

TargetBinding ==
    \A cell \in applied : actualEffects[cell] = cell

PublicationBinding ==
    writerStatus \in {"published", "committed"} =>
        /\ applied = Cells
        /\ Even(publishedEpoch)
        /\ publishedEpoch = acquiredFrom + 2
        /\ epoch = publishedEpoch

AbortNoninterference ==
    writerStatus = "aborted" =>
        /\ applied = {}
        /\ heap = [cell \in Cells |-> 0]

StableReaderSnapshot ==
    readerStatus = "committed" =>
        /\ readerRead = Cells
        /\ readerValues[X] = readerValues[Y]
        /\ readerValues[X] \in {0, 1}

SequentialOrder ==
    /\ (applied # {} => writerStatus \in {"acquired", "published", "committed", "aborted"})
    /\ (writerStatus = "committed" => publishedEpoch # 0)

CompositionInvariant ==
    /\ IdentityBinding
    /\ AccessBinding
    /\ AcquisitionBinding
    /\ OddEpochExclusion
    /\ TargetBinding
    /\ PublicationBinding
    /\ AbortNoninterference
    /\ StableReaderSnapshot
    /\ SequentialOrder

Init ==
    /\ epoch = 0
    /\ heap = [cell \in Cells |-> 0]
    /\ registry = {}
    /\ readerDeclaration = {}
    /\ writerDeclaration = {}
    /\ writerStatus = "new"
    /\ writerStart = 0
    /\ acquiredFrom = 0
    /\ publishedEpoch = 0
    /\ readerStatus = "new"
    /\ readerStart = 0
    /\ readerRead = {}
    /\ readerValues = [cell \in Cells |-> NULL]
    /\ applied = {}
    /\ actualEffects = [cell \in Cells |-> NULL]
    /\ advanced = FALSE

BeginWriter ==
    /\ writerStatus = "new"
    /\ writerStatus' = IF Even(epoch) THEN "active" ELSE "aborted"
    /\ writerStart' = epoch
    /\ registry' = registry \cup {Writer}
    /\ writerDeclaration' = Cells
    /\ UNCHANGED <<
        epoch, heap, readerDeclaration,
        acquiredFrom, publishedEpoch,
        readerStatus, readerStart, readerRead, readerValues,
        applied, actualEffects, advanced
        >>

BeginReader ==
    /\ readerStatus = "new"
    /\ readerStatus' = IF Even(epoch) THEN "active" ELSE "aborted"
    /\ readerStart' = epoch
    /\ registry' =
        IF Fault = "ReuseIdentity" THEN registry \cup {Writer}
        ELSE registry \cup {Reader}
    /\ readerDeclaration' =
        IF Fault = "UndeclaredRead" THEN {X} ELSE Cells
    /\ UNCHANGED <<
        epoch, heap, writerDeclaration,
        writerStatus, writerStart, acquiredFrom, publishedEpoch,
        readerRead, readerValues,
        applied, actualEffects, advanced
        >>

AdvanceEpoch ==
    /\ Fault = "StaleAcquire"
    /\ writerStatus = "active"
    /\ ~advanced
    /\ Even(epoch)
    /\ epoch' = epoch + 2
    /\ advanced' = TRUE
    /\ UNCHANGED <<
        heap, registry, readerDeclaration, writerDeclaration,
        writerStatus, writerStart, acquiredFrom, publishedEpoch,
        readerStatus, readerStart, readerRead, readerValues,
        applied, actualEffects
        >>

AcquireWriter ==
    /\ writerStatus = "active"
    /\ Even(epoch)
    /\ (epoch = writerStart \/ Fault = "StaleAcquire")
    /\ acquiredFrom' = epoch
    /\ epoch' = epoch + 1
    /\ writerStatus' = "acquired"
    /\ UNCHANGED <<
        heap, registry, readerDeclaration, writerDeclaration,
        writerStart, publishedEpoch,
        readerStatus, readerStart, readerRead, readerValues,
        applied, actualEffects, advanced
        >>

ApplyWriter(cell) ==
    /\ writerStatus = "acquired"
    /\ cell \in Cells \ applied
    /\ LET actual ==
            IF Fault = "MisdirectWrite" /\ cell = X THEN Y ELSE cell
       IN /\ heap' = [heap EXCEPT ![actual] = 1]
          /\ actualEffects' = [actualEffects EXCEPT ![cell] = actual]
    /\ applied' = applied \cup {cell}
    /\ IF Fault = "AbortAfterWrite" /\ applied = {}
       THEN /\ writerStatus' = "aborted"
            /\ epoch' = epoch + 1
       ELSE /\ writerStatus' = writerStatus
            /\ epoch' = epoch
    /\ UNCHANGED <<
        registry, readerDeclaration, writerDeclaration,
        writerStart, acquiredFrom, publishedEpoch,
        readerStatus, readerStart, readerRead, readerValues,
        advanced
        >>

PublishWriter ==
    /\ writerStatus = "acquired"
    /\ applied = Cells \/ (Fault = "EarlyPublish" /\ applied # {})
    /\ epoch' = epoch + 1
    /\ publishedEpoch' = epoch + 1
    /\ writerStatus' = "published"
    /\ UNCHANGED <<
        heap, registry, readerDeclaration, writerDeclaration,
        writerStart, acquiredFrom,
        readerStatus, readerStart, readerRead, readerValues,
        applied, actualEffects, advanced
        >>

CommitWriter ==
    /\ (writerStatus = "published"
        \/ (Fault = "SkipPublication" /\ writerStatus = "acquired"))
    /\ writerStatus' = "committed"
    /\ UNCHANGED <<
        epoch, heap, registry, readerDeclaration, writerDeclaration,
        writerStart, acquiredFrom, publishedEpoch,
        readerStatus, readerStart, readerRead, readerValues,
        applied, actualEffects, advanced
        >>

ReadReader(cell) ==
    /\ readerStatus = "active"
    /\ cell \in Cells \ readerRead
    /\ IF Fault = "IgnoreEpochValidation" \/ (Even(epoch) /\ epoch = readerStart)
       THEN /\ readerValues' = [readerValues EXCEPT ![cell] = heap[cell]]
            /\ readerRead' = readerRead \cup {cell}
            /\ readerStatus' = readerStatus
       ELSE /\ readerValues' = readerValues
            /\ readerRead' = readerRead
            /\ readerStatus' = "aborted"
    /\ UNCHANGED <<
        epoch, heap, registry, readerDeclaration, writerDeclaration,
        writerStatus, writerStart, acquiredFrom, publishedEpoch,
        readerStart, applied, actualEffects, advanced
        >>

CommitReader ==
    /\ readerStatus = "active"
    /\ readerRead = Cells
    /\ readerStatus' = "committed"
    /\ UNCHANGED <<
        epoch, heap, registry, readerDeclaration, writerDeclaration,
        writerStatus, writerStart, acquiredFrom, publishedEpoch,
        readerStart, readerRead, readerValues,
        applied, actualEffects, advanced
        >>

Next ==
    \/ BeginWriter
    \/ BeginReader
    \/ AdvanceEpoch
    \/ AcquireWriter
    \/ \E cell \in Cells : ApplyWriter(cell)
    \/ PublishWriter
    \/ CommitWriter
    \/ \E cell \in Cells : ReadReader(cell)
    \/ CommitReader

Spec == Init /\ [][Next]_vars

====
