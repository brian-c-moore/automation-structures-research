---- MODULE ConstructionAdmissionRejections ----
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
AllGuaranteeKinds == GuaranteeKinds

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
RelationalPropertyClass ==
    [guarantee \in RegisteredGuarantees |-> "relational"]
GuaranteeBoundaryOf ==
    [guarantee \in RegisteredGuarantees |-> "boundary"]
GuaranteeFailureCeilingOf ==
    [guarantee \in RegisteredGuarantees |-> "declared-only"]

ValidStaticAdmission ==
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
        AllGuaranteeKinds, TRUE, TRUE)

EmptyInstances == {}
EmptyStructureOf == [instance \in EmptyInstances |-> "structure"]
EmptyParameters == [instance \in EmptyInstances |-> "domain"]

RejectsEmptyInstances ==
    ~ConstructionStaticAdmission(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        EmptyInstances, EmptyStructureOf, ParameterDomain,
        ParameterDomainOf, EmptyParameters,
        SelectedFamilies, DeclaredGlobalAssumptions,
        LibraryPremises, DeploymentPremises, DischargedPremises,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        AllGuaranteeKinds, TRUE, TRUE)

UninstantiatedInstances == {"structure-instance"}
UninstantiatedStructureOf ==
    [instance \in UninstantiatedInstances |-> "structure"]
UninstantiatedParameters ==
    [instance \in UninstantiatedInstances |-> "domain"]

RejectsUninstantiatedSelection ==
    ~ConstructionStaticAdmission(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        UninstantiatedInstances, UninstantiatedStructureOf,
        ParameterDomain, ParameterDomainOf, UninstantiatedParameters,
        SelectedFamilies, DeclaredGlobalAssumptions,
        LibraryPremises, DeploymentPremises, DischargedPremises,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        AllGuaranteeKinds, TRUE, TRUE)

MissingCoreFamilies == {"obligation", "ownership-assurance"}
MissingCoreGuarantees == {"obligation-g", "assurance-g"}
MissingCoreGuaranteeFamily ==
    [guarantee \in MissingCoreGuarantees |->
        IF guarantee = "obligation-g"
          THEN "obligation"
          ELSE "ownership-assurance"]
MissingCoreGuaranteeKind ==
    [guarantee \in MissingCoreGuarantees |-> "conditional"]
MissingCorePropertyClass ==
    [guarantee \in MissingCoreGuarantees |-> "safety"]
MissingCoreBoundary ==
    [guarantee \in MissingCoreGuarantees |-> "boundary"]
MissingCoreFailureCeiling ==
    [guarantee \in MissingCoreGuarantees |-> "declared-only"]
MissingCoreLibraryPremises ==
    GlobalModelingAssumptionNames
      \cup SelectedFamilyPremiseNames(MissingCoreFamilies)
MissingCoreDischargedPremises ==
    MissingCoreLibraryPremises \cup DeploymentPremises

RejectsMissingRequiredRefinement ==
    ~ConstructionStaticAdmission(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        MissingCoreFamilies, DeclaredGlobalAssumptions,
        MissingCoreLibraryPremises, DeploymentPremises,
        MissingCoreDischargedPremises,
        MissingCoreGuarantees, BoundaryIds, FailureCeilings,
        MissingCoreGuaranteeFamily, MissingCoreGuaranteeKind,
        MissingCorePropertyClass, MissingCoreBoundary,
        MissingCoreFailureCeiling,
        AllGuaranteeKinds, TRUE, TRUE)

RejectsRelationalRegistration ==
    ~ConstructionStaticAdmission(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies, DeclaredGlobalAssumptions,
        LibraryPremises, DeploymentPremises, DischargedPremises,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, RelationalPropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        AllGuaranteeKinds, TRUE, TRUE)

WrongPropertyClass ==
    [guarantee \in RegisteredGuarantees |->
        CASE guarantee = "obligation-g" -> "liveness"
          [] guarantee = "assurance-g" -> "safety"
          [] OTHER -> "safety"]

RejectsPropertyFamilyMismatch ==
    ~ConstructionStaticAdmission(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies, DeclaredGlobalAssumptions,
        LibraryPremises, DeploymentPremises, DischargedPremises,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, WrongPropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        AllGuaranteeKinds, TRUE, TRUE)

PreventionGuaranteeKind ==
    [guarantee \in RegisteredGuarantees |-> "prevention"]

RejectsUnsupportedGuaranteeKind ==
    ~ConstructionStaticAdmission(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies, DeclaredGlobalAssumptions,
        LibraryPremises, DeploymentPremises, DischargedPremises,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, PreventionGuaranteeKind,
        GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        {"conditional", "lost"}, TRUE, TRUE)

Init == progressState = "unused"
Next == UNCHANGED progressState
Spec == Init /\ [][Next]_progressState

====
