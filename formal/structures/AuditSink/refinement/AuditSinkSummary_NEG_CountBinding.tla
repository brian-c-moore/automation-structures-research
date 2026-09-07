---- MODULE AuditSinkSummary_NEG_CountBinding ----
\* Candidate summary observation profile of the existing AuditSink.
\* count/carry/latest are proposed executable observations; history is a
\* logical witness only. This model supplies no Rust implementation, storage
\* bound measurement, retained evidence, replay or tamper-detection claim.
\* Donor: AuditSinkImplRefinesSpec (explicit state/action/observation mapping).
EXTENDS Naturals, Sequences

CONSTANTS Operations, MaxLogLen, Hash(_, _)
VARIABLES history, count, carry, latest
vars == <<history, count, carry, latest>>

AS == INSTANCE AuditSink WITH log <- history, last_hash <- carry

HashImpl(previous, operation) == (previous * 3 + operation + 1) % 100
Entry == [operation : Operations, prev_hash : Nat, hash : Nat]

BasicTypes ==
    /\ history \in Seq(Entry)
    /\ count \in Nat
    /\ carry \in Nat
    /\ latest \in Seq(Operations)
    /\ Len(latest) <= 1

CountBinding == count = Len(history)
CarryBinding ==
    carry = IF Len(history) = 0 THEN 0 ELSE history[Len(history)].hash
LatestBinding ==
    latest = IF Len(history) = 0 THEN <<>> ELSE <<history[Len(history)].operation>>
CapacityBound == count <= MaxLogLen
SummaryBinding == CountBinding /\ CarryBinding /\ LatestBinding
ChainSafety == AS!ChainIntegrity /\ AS!HashConsistency /\ AS!HashBindsContent

Init ==
    /\ history = <<>>
    /\ count = 0
    /\ carry = 0
    /\ latest = <<>>

\* The executable guard/effect refers only to count/carry/latest and the input.
\* LogicalHistoryStep is erased by a future checked implementation; it is not
\* an executable log and cannot satisfy an external evidence request.
CompactRecord(operation) ==
    /\ operation \in Operations
    /\ count < MaxLogLen
    /\ count' = count + 2
    /\ carry' = Hash(carry, operation)
    /\ latest' = <<operation>>

LogicalHistoryStep(operation) ==
    history' = Append(history,
        [operation |-> operation, prev_hash |-> carry,
         hash |-> Hash(carry, operation)])

Record(operation) == CompactRecord(operation) /\ LogicalHistoryStep(operation)

RefusedRecord(operation) ==
    /\ operation \in Operations
    /\ count >= MaxLogLen
    /\ UNCHANGED vars

Next == \E operation \in Operations : Record(operation) \/ RefusedRecord(operation)
Spec == Init /\ [][Next]_vars

GuardAgreement == (count < MaxLogLen) = (Len(history) < MaxLogLen)
AuditRefinement == AS!Spec
====
