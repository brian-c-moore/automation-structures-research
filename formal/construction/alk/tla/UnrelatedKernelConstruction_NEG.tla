---- MODULE UnrelatedKernelConstruction_NEG ----
EXTENDS ALKConstructionTheoremWitness

MismatchedSelectedStructuresForKernel == {"ResourceRegistry", "Sequential"}

MismatchedKernelStructureSelectionHeld ==
    KernelSelectionGuaranteeBinding(
        Claims, Structures, ExecutionModalities, Obligations,
        States,
        SelectedStructures, SelectedExecutionModality,
        ClaimObligations, ObligationPropertyClass, ObligationStates,
        MismatchedSelectedStructuresForKernel, SelectedExecutionCarrier,
        RegisteredGuarantees, GuaranteeFamily,
        GuaranteePropertyClass, GuaranteeObligations, SafeStates)

ShadowExecutionModalityObligationOccurrences ==
    [modality \in ExecutionModalities |->
        IF modality = "Sequential"
          THEN {"Sequential!TypeInvariant"}
          ELSE ExecutionModalityObligationOccurrences[modality]]
ShadowClaimObligationOccurrences ==
    [claim \in Claims |->
        RequiredALKObligationOccurrences(
            SelectedStructures[claim],
            SelectedExecutionModality[claim],
            StructureObligationOccurrences,
            ShadowExecutionModalityObligationOccurrences,
            CompositionSeamObligationOccurrences[claim])]
ShadowClaimObligations ==
    [claim \in Claims |->
        RequiredALKObligations(
            SelectedStructures[claim],
            SelectedExecutionModality[claim],
            StructureObligationOccurrences,
            ShadowExecutionModalityObligationOccurrences,
            CompositionSeamObligationOccurrences[claim],
            NormalizedKeyOf)]
ShadowGuaranteeObligations ==
    [guarantee \in RegisteredGuarantees |->
        IF GuaranteeFamily[guarantee]
             \in {"obligation", "progress", "refinement"}
          THEN ShadowClaimObligations["bounded-claim"]
          ELSE {}]

ShadowSelectionAdjacentBoundaryHeld ==
    /\ ALKConstructionSelectionTyped(
           Claims, Structures, ExecutionModalities,
           ObligationOccurrences, Obligations,
           StructureObligationOccurrences,
           ShadowExecutionModalityObligationOccurrences,
           NormalizedKeyOf,
           SelectedStructures, SelectedExecutionModality,
           CompositionSeamObligationOccurrences,
           ShadowClaimObligationOccurrences,
           ShadowClaimObligations)
    /\ KernelSelectionGuaranteeBinding(
           Claims, Structures, ExecutionModalities, Obligations,
           States,
           SelectedStructures, SelectedExecutionModality,
           ShadowClaimObligations, ObligationPropertyClass,
           ObligationStates,
           SelectedStructuresForKernel, SelectedExecutionCarrier,
           RegisteredGuarantees, GuaranteeFamily,
           GuaranteePropertyClass, ShadowGuaranteeObligations,
           SafeStates)

ShadowRetainedRegistryBindingHeld ==
    ExactRetainedObligationRegistryBinding(
        Structures, ExecutionModalities,
        ObligationOccurrences, Obligations,
        StructureObligationOccurrences,
        ShadowExecutionModalityObligationOccurrences,
        NormalizedKeyOf, ObligationPropertyClass,
        RegistryStructureNames, RegistryExecutionModalityNames,
        RegistryObligationOccurrenceNames,
        RegistryNormalizedObligationNames,
        RegistryCarrierObligationOccurrences,
        RegistryNormalizedKeyOf,
        RegistryObligationPropertyClassOf)

MismatchedKernelSelectionHeld ==
    MismatchedKernelStructureSelectionHeld \/ ShadowRetainedRegistryBindingHeld

NegativeControlExpected == NegativeControlGate(MismatchedKernelSelectionHeld)

====
