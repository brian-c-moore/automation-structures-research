---- MODULE AuditCustody ----
EXTENDS Naturals, TLC

CONSTANTS NoFault, ReceiptWithoutAcceptance, FaultMode
ASSUME FaultMode \in {NoFault, ReceiptWithoutAcceptance}

VARIABLES phase,
          strictMode,
          partitioned,
          storeHealthy,
          checkReachable,
          independentReplica,
          requestSucceeded,
          localEvent,
          externalAccepted,
          receipt,
          retained,
          detected,
          recovered

vars == <<phase, strictMode, partitioned, storeHealthy, checkReachable,
          independentReplica, requestSucceeded, localEvent, externalAccepted,
          receipt, retained, detected, recovered>>

Init ==
    /\ phase = "Ready"
    /\ strictMode \in BOOLEAN
    /\ partitioned \in BOOLEAN
    /\ storeHealthy \in BOOLEAN
    /\ checkReachable \in BOOLEAN
    /\ independentReplica \in BOOLEAN
    /\ requestSucceeded = FALSE
    /\ localEvent = FALSE
    /\ externalAccepted = FALSE
    /\ receipt = FALSE
    /\ retained = FALSE
    /\ detected = FALSE
    /\ recovered = FALSE

CreateAndExport ==
    /\ phase = "Ready"
    /\ localEvent' = TRUE
    /\ externalAccepted' = storeHealthy /\ ~partitioned
    /\ receipt' = ((storeHealthy /\ ~partitioned)
                   \/ FaultMode = ReceiptWithoutAcceptance)
    /\ retained' = storeHealthy /\ ~partitioned
    /\ requestSucceeded' =
          IF strictMode
          THEN (storeHealthy /\ ~partitioned)
               \/ FaultMode = ReceiptWithoutAcceptance
          ELSE TRUE
    /\ phase' = IF storeHealthy /\ ~partitioned THEN "Stored" ELSE "Done"
    /\ detected' = FALSE
    /\ recovered' = FALSE
    /\ UNCHANGED <<strictMode, partitioned, storeHealthy,
                   checkReachable, independentReplica>>

RetentionHolds ==
    /\ phase = "Stored"
    /\ phase' = "Done"
    /\ UNCHANGED <<strictMode, partitioned, storeHealthy, checkReachable,
                   independentReplica, requestSucceeded, localEvent,
                   externalAccepted, receipt, retained, detected, recovered>>

RetentionFails ==
    /\ phase = "Stored"
    /\ phase' = "Done"
    /\ retained' = FALSE
    /\ detected' = checkReachable
    /\ recovered' = checkReachable /\ independentReplica
    /\ UNCHANGED <<strictMode, partitioned, storeHealthy, checkReachable,
                   independentReplica, requestSucceeded, localEvent,
                   externalAccepted, receipt>>

Done ==
    /\ phase = "Done"
    /\ UNCHANGED vars

Next == CreateAndExport \/ RetentionHolds \/ RetentionFails \/ Done
Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ phase \in {"Ready", "Stored", "Done"}
    /\ strictMode \in BOOLEAN
    /\ partitioned \in BOOLEAN
    /\ storeHealthy \in BOOLEAN
    /\ checkReachable \in BOOLEAN
    /\ independentReplica \in BOOLEAN
    /\ requestSucceeded \in BOOLEAN
    /\ localEvent \in BOOLEAN
    /\ externalAccepted \in BOOLEAN
    /\ receipt \in BOOLEAN
    /\ retained \in BOOLEAN
    /\ detected \in BOOLEAN
    /\ recovered \in BOOLEAN

StrictReceiptSound ==
    (phase = "Done" /\ strictMode /\ requestSucceeded)
    => (localEvent /\ receipt /\ externalAccepted)

DetectionSound ==
    (phase = "Done" /\ externalAccepted /\ ~retained /\ checkReachable)
    => detected

RecoverySound ==
    (phase = "Done" /\ externalAccepted /\ ~retained
      /\ checkReachable /\ independentReplica)
    => recovered

PartitionCeiling ==
    (phase = "Done" /\ strictMode /\ partitioned /\ ~storeHealthy)
    => ~requestSucceeded

====
