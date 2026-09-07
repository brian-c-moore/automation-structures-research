---- MODULE Records ----
\* ====================================================================
\* SHARED PRIMITIVE: RECORD TYPE
\*
\* A record type over a finite CONSTANT domain, kept small for TLC.
\* No module under Execution Modalities extends or instantiates this
\* one: StreamGraph declares its own RecordDomain and StepGraph models
\* no records at all.
\* ====================================================================
EXTENDS Naturals

CONSTANTS RecordDomain   \* finite set, e.g. {0,1} or 0..3

\* A record is just an element of RecordDomain.
IsRecord(r) == r \in RecordDomain

\* Identity transformation, used as a default operator function.
Identity(r) == r
====
