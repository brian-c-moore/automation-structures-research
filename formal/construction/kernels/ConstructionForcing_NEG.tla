---- MODULE ConstructionForcing_NEG ----
EXTENDS ConstructionKernel, TLC

RetainedStructures == {"structure", "execution"}
SelectedStructures == RetainedStructures
RetainedExecutionCarriers == {"execution"}
SelectedExecutionCarrier == "execution"
Instances == {"structure-instance", "execution-instance"}
StructureOf ==
    [instance \in Instances |->
        IF instance = "structure-instance" THEN "structure" ELSE "execution"]
ParameterDomain == {"domain"}
ParameterDomainOf ==
    [structure \in SelectedStructures |-> ParameterDomain]
Parameters == [instance \in Instances |-> "domain"]
SelectedFamilies == RequiredConstructionFamilies

DeclaredGlobalAssumptions == GlobalModelingAssumptionNames
LibraryPremises ==
    GlobalModelingAssumptionNames
      \cup SelectedFamilyPremiseNames(SelectedFamilies)
DeploymentPremises == {"runtime-rely"}
DischargedPremises == LibraryPremises \cup DeploymentPremises

RegisteredGuarantees == {"obligation-g", "assurance-g", "refinement-g"}
BoundaryIds == {"boundary"}
FailureCeilings == {"declared-only"}
GuaranteeFamily ==
    [guarantee \in RegisteredGuarantees |->
        CASE guarantee = "obligation-g" -> "obligation"
          [] guarantee = "assurance-g" -> "ownership-assurance"
          [] OTHER -> "refinement"]
GuaranteeKindOf ==
    [guarantee \in RegisteredGuarantees |-> "conditional"]
GuaranteePropertyClass ==
    [guarantee \in RegisteredGuarantees |-> "safety"]
GuaranteeBoundaryOf ==
    [guarantee \in RegisteredGuarantees |-> "boundary"]
GuaranteeFailureCeilingOf ==
    [guarantee \in RegisteredGuarantees |-> "declared-only"]

States == {"safe", "bad"}
InitialStates == {"safe"}
ObligationStates == {"safe"}
ViolatingSystemSteps == {<<"safe", "bad">>}
EnvironmentSteps == {}
RelySteps == {}

ObligationPremises ==
    ObligationPreservationPremises(
        States, InitialStates, ObligationStates,
        ViolatingSystemSteps, EnvironmentSteps, RelySteps)

StaticAdmissionHeld ==
    ConstructionStaticAdmission(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies, DeclaredGlobalAssumptions,
        LibraryPremises, DeploymentPremises, DischargedPremises,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        GuaranteeKinds, TRUE, TRUE)

FullAdmissionRejected ==
    ~ConstructionAdmitted(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies, DeclaredGlobalAssumptions,
        LibraryPremises, DeploymentPremises, DischargedPremises,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        GuaranteeKinds, TRUE, TRUE,
        ObligationPremises, TRUE, TRUE, TRUE, TRUE, TRUE)

VARIABLE state
vars == <<state, progressState>>

Init ==
    /\ state = "safe"
    /\ progressState = "unused"

Corrupt ==
    /\ state = "safe"
    /\ state' = "bad"
    /\ UNCHANGED progressState

Next == Corrupt \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

AdvertisedObligation == state \in ObligationStates

====
