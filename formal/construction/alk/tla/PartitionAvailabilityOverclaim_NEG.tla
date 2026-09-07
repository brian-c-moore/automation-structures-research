---- MODULE PartitionAvailabilityOverclaim_NEG ----
EXTENDS ALKSemanticModelWitness

PartitionOverclaim ==
    [claim \in Claims |->
        [failureClass \in ALKFailureClasses |->
            IF failureClass = "partition"
              THEN {"prevention"}
            ELSE AdvertisedGuaranteeUnderFailure[claim][failureClass]]]

PartitionCeilingRespected ==
    FailureCeilingsRespected(
        Claims, PartitionOverclaim, GuaranteeUnderFailure)

NegativeControlExpected == NegativeControlGate(PartitionCeilingRespected)

====
