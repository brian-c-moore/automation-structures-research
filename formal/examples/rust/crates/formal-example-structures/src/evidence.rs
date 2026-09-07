use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ArtifactFamily {
    ClassicalSchema,
    CryptoSchema,
    ClassicalAlgorithm,
    CryptographicAlgorithm,
    CorpusAssessment,
    DomainExample,
    IntegratedReconstruction,
    DomainPoc,
    CrossExampleRelation,
    AbsenceControl,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum EvidenceRole {
    ReusableSchema,
    CorpusWitness,
    CorpusAssessment,
    DomainReconstruction,
    SourceReconstruction,
    ProblemFirstConstruction,
    CrossExampleRelation,
    AbsenceControl,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum AuthorityKind {
    ProblemContract,
    ProjectDecomposition,
    PrimaryPaper,
    PrimaryTextbook,
    NormativeStandard,
    PublishedFixture,
    ExecutableAuthority,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SourceAuthority {
    pub id: String,
    pub kind: AuthorityKind,
    pub locator: String,
    pub edition: String,
    pub scope: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TerritoryRecord {
    pub authorities: Vec<SourceAuthority>,
    pub included_behavior: Vec<String>,
    pub omissions: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct NativeProblemRecord {
    pub actors: Vec<String>,
    pub state: Vec<String>,
    pub transitions: Vec<String>,
    pub commitments: Vec<String>,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
    pub failures: Vec<String>,
    pub obligations: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct StrippedRole {
    pub role: String,
    pub domain_binding: String,
    pub preserved_relation: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ConstructionStratum {
    Catalog,
    Connective,
    Domain,
    Runtime,
    Conventional,
    NewGeneric,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ConstructionOutcome {
    CatalogComposition,
    UnidentifiedShapeCandidate,
    AbstractionLayerLocalShapeCandidate,
    FaultyDecomposition,
    Blocked,
    Rejected,
}

impl ConstructionOutcome {
    pub fn supports_reconstruction(&self) -> bool {
        matches!(self, Self::CatalogComposition)
    }

    fn is_candidate(&self) -> bool {
        matches!(
            self,
            Self::UnidentifiedShapeCandidate | Self::AbstractionLayerLocalShapeCandidate
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ConstructionNode {
    pub id: String,
    pub stratum: ConstructionStratum,
    pub implementation_identity: String,
    pub responsibility: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ConstructionEdge {
    pub before: String,
    pub after: String,
    pub obligation: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CandidateShapeAssessment {
    pub abstraction_layer: Option<String>,
    pub reusable_obligation: String,
    pub failed_catalog_bindings: Vec<String>,
    pub failed_cross_layer_substitutions: Vec<String>,
    pub control_bindings: Vec<CandidateControlBinding>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CandidateControlBinding {
    pub control_id: String,
    pub node_id: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ConstructionAccount {
    pub outcome: ConstructionOutcome,
    pub nodes: Vec<ConstructionNode>,
    pub edges: Vec<ConstructionEdge>,
    pub execution_carrier: String,
    pub governed_commit_points: Vec<String>,
    pub permitted_host_material: Vec<String>,
    pub scope_delta: Vec<String>,
    pub candidate_assessment: Option<CandidateShapeAssessment>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct OracleRecord {
    pub id: String,
    pub method: String,
    pub implementation_identity: String,
    pub imports_shared_structures: bool,
    pub calls_construction_helpers: bool,
    pub expected_data: Vec<String>,
    pub equivalence_relation: String,
    pub common_mode_risks: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ControlClass {
    SourceInput,
    Construction,
    Oracle,
    Relation,
    Rely,
    ConventionalPath,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ControlRecord {
    pub id: String,
    pub class: ControlClass,
    pub target: String,
    pub mutation: String,
    pub expected_failure: String,
    pub adjacent_checks: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum RelationAssuranceClass {
    SharedExecutableSubgraph,
    CanonicalIndependentInstantiation,
    BoundedSemanticCorrespondence,
    VocabularyResemblance,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SharedImplementationBinding {
    pub member_id: String,
    pub node_id: String,
    pub implementation_identity: String,
    pub claim_path: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct MemberEdgeControlBinding {
    pub member_id: String,
    pub before: String,
    pub after: String,
    pub control_id: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct RelationContract {
    pub assurance_class: RelationAssuranceClass,
    pub members: Vec<String>,
    pub shared_nodes: Vec<String>,
    pub shared_edges: Vec<ConstructionEdge>,
    pub implementation_bindings: Vec<SharedImplementationBinding>,
    pub relation_control_ids: Vec<String>,
    pub member_edge_controls: Vec<MemberEdgeControlBinding>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ClaimBoundary {
    pub claim: String,
    pub claim_ceiling: String,
    pub residuals: Vec<String>,
    pub falsifiers: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DacBaseRecord {
    pub id: String,
    pub name: String,
    pub family: ArtifactFamily,
    pub evidence_role: EvidenceRole,
    pub territory: TerritoryRecord,
    pub native_problem: NativeProblemRecord,
    pub stripped_roles: Vec<StrippedRole>,
    pub construction: ConstructionAccount,
    pub relies: Vec<String>,
    pub oracle: Option<OracleRecord>,
    pub controls: Vec<ControlRecord>,
    pub relation: Option<RelationContract>,
    pub boundary: ClaimBoundary,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct InstanceDelta {
    pub id: String,
    pub name: String,
    pub family: ArtifactFamily,
    pub evidence_role: EvidenceRole,
    pub base_id: String,
    pub base_evidence_identity: String,
    pub territory: Option<TerritoryRecord>,
    pub native_problem: Option<NativeProblemRecord>,
    pub stripped_roles: Option<Vec<StrippedRole>>,
    pub added_nodes: Vec<ConstructionNode>,
    pub assembly_seams: Vec<ConstructionEdge>,
    pub added_relies: Vec<String>,
    pub replaced_relies: Vec<RelyReplacement>,
    pub inherited_control_bindings: Vec<String>,
    pub added_controls: Vec<ControlRecord>,
    pub oracle: Option<OracleRecord>,
    pub boundary: ClaimBoundary,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct RelyReplacement {
    pub previous: String,
    pub replacement: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RecordDefinition {
    Base(Box<DacBaseRecord>),
    Instance(Box<InstanceDelta>),
}

impl RecordDefinition {
    pub fn id(&self) -> &str {
        match self {
            Self::Base(record) => &record.id,
            Self::Instance(delta) => &delta.id,
        }
    }
}

pub fn evidence_content_identity(record: &DacBaseRecord) -> Result<String, String> {
    let encoded = serde_json::to_vec(record)
        .map_err(|error| format!("cannot serialize evidence record: {error}"))?;
    let digest = Sha256::digest(encoded);
    Ok(format!("sha256:{digest:x}"))
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct MaterializedDacRecord {
    pub schema: String,
    pub inherited_from: Vec<String>,
    pub base_evidence_identity: Option<String>,
    pub instance_delta: Option<InstanceDelta>,
    #[serde(flatten)]
    pub record: DacBaseRecord,
}

#[derive(Clone, Debug)]
pub struct EvidenceRegistry {
    definitions: BTreeMap<String, RecordDefinition>,
}

impl EvidenceRegistry {
    pub fn new(definitions: Vec<RecordDefinition>) -> Result<Self, String> {
        let mut indexed = BTreeMap::new();
        for definition in definitions {
            let id = definition.id().to_string();
            if id.is_empty() || indexed.insert(id.clone(), definition).is_some() {
                return Err(format!("evidence record ID {id:?} is empty or duplicated"));
            }
        }
        let registry = Self {
            definitions: indexed,
        };
        for id in registry.definitions.keys() {
            registry.materialize(id)?;
        }
        registry.validate_cross_record_relations()?;
        Ok(registry)
    }

    pub fn ids(&self) -> Vec<String> {
        self.definitions.keys().cloned().collect()
    }

    pub fn materialize(&self, id: &str) -> Result<MaterializedDacRecord, String> {
        let definition = self
            .definitions
            .get(id)
            .ok_or_else(|| format!("unknown evidence record {id}"))?;
        let materialized = match definition {
            RecordDefinition::Base(record) => MaterializedDacRecord {
                schema: "formal-example-dac-record-v1".to_string(),
                inherited_from: Vec::new(),
                base_evidence_identity: None,
                instance_delta: None,
                record: record.as_ref().clone(),
            },
            RecordDefinition::Instance(delta) => {
                let base = self.definitions.get(&delta.base_id).ok_or_else(|| {
                    format!("{} inherits missing base {}", delta.id, delta.base_id)
                })?;
                let RecordDefinition::Base(base) = base else {
                    return Err(format!("{} inherits a non-base record", delta.id));
                };
                let expected_identity = evidence_content_identity(base)?;
                if delta.base_evidence_identity != expected_identity {
                    return Err(format!(
                        "{} base evidence identity does not match {}",
                        delta.id, delta.base_id
                    ));
                }
                let mut rely_replacements = BTreeMap::new();
                for replacement in &delta.replaced_relies {
                    require_text("previous rely", &replacement.previous)?;
                    require_text("replacement rely", &replacement.replacement)?;
                    if replacement.previous == replacement.replacement {
                        return Err(format!("{} replaces a rely with itself", delta.id));
                    }
                    let matches: Vec<_> = base
                        .relies
                        .iter()
                        .enumerate()
                        .filter(|(_, rely)| *rely == &replacement.previous)
                        .map(|(index, _)| index)
                        .collect();
                    if matches.len() != 1 {
                        return Err(format!(
                            "{} rely replacement does not resolve exactly once in {}",
                            delta.id, delta.base_id
                        ));
                    }
                    if rely_replacements
                        .insert(matches[0], replacement.replacement.clone())
                        .is_some()
                    {
                        return Err(format!(
                            "{} replaces the same base rely more than once",
                            delta.id
                        ));
                    }
                }
                let mut joined = base.as_ref().clone();
                joined.id = delta.id.clone();
                joined.name = delta.name.clone();
                joined.family = delta.family.clone();
                joined.evidence_role = delta.evidence_role.clone();
                if let Some(territory) = &delta.territory {
                    joined.territory = territory.clone();
                }
                if let Some(native_problem) = &delta.native_problem {
                    joined.native_problem = native_problem.clone();
                }
                if let Some(stripped_roles) = &delta.stripped_roles {
                    joined.stripped_roles = stripped_roles.clone();
                }
                joined
                    .construction
                    .nodes
                    .extend(delta.added_nodes.iter().cloned());
                joined
                    .construction
                    .edges
                    .extend(delta.assembly_seams.iter().cloned());
                for (index, replacement) in rely_replacements {
                    joined.relies[index] = replacement;
                }
                joined.relies.extend(delta.added_relies.iter().cloned());
                joined.controls.extend(delta.added_controls.iter().cloned());
                if let Some(oracle) = &delta.oracle {
                    joined.oracle = Some(oracle.clone());
                }
                joined.boundary = delta.boundary.clone();
                MaterializedDacRecord {
                    schema: "formal-example-dac-record-v1".to_string(),
                    inherited_from: vec![delta.base_id.clone()],
                    base_evidence_identity: Some(delta.base_evidence_identity.clone()),
                    instance_delta: Some(delta.as_ref().clone()),
                    record: joined,
                }
            }
        };
        materialized.validate()?;
        Ok(materialized)
    }

    fn validate_cross_record_relations(&self) -> Result<(), String> {
        for id in self.definitions.keys() {
            let record = self.materialize(id)?;
            let Some(relation) = &record.record.relation else {
                continue;
            };
            for binding in &relation.implementation_bindings {
                if !relation.members.contains(&binding.member_id) {
                    return Err(format!(
                        "relation {id} binds an implementation from non-member {}",
                        binding.member_id
                    ));
                }
                if !relation.shared_nodes.contains(&binding.node_id) {
                    return Err(format!(
                        "relation {id} binds an implementation for unregistered node {}",
                        binding.node_id
                    ));
                }
                let member = self.materialize(&binding.member_id)?;
                let construction_node = member
                    .record
                    .construction
                    .nodes
                    .iter()
                    .find(|node| node.id == binding.node_id)
                    .ok_or_else(|| {
                        format!(
                            "relation {id} binds node {} absent from member {}",
                            binding.node_id, binding.member_id
                        )
                    })?;
                if construction_node.implementation_identity != binding.implementation_identity {
                    return Err(format!(
                        "relation {id} implementation identity for {} on {} differs from the member construction account",
                        binding.node_id, binding.member_id
                    ));
                }
            }
            for binding in &relation.member_edge_controls {
                if !relation.members.contains(&binding.member_id) {
                    return Err(format!(
                        "relation {id} binds an edge control from non-member {}",
                        binding.member_id
                    ));
                }
                if !relation
                    .shared_edges
                    .iter()
                    .any(|edge| edge.before == binding.before && edge.after == binding.after)
                {
                    return Err(format!(
                        "relation {id} binds {} to an unregistered shared edge",
                        binding.control_id
                    ));
                }
                let member = self.materialize(&binding.member_id)?;
                let control = member
                    .record
                    .controls
                    .iter()
                    .find(|control| control.id == binding.control_id)
                    .ok_or_else(|| {
                        format!(
                            "relation {id} binds missing member control {}",
                            binding.control_id
                        )
                    })?;
                if control.class != ControlClass::Construction {
                    return Err(format!(
                        "relation {id} edge control {} is not a construction control",
                        binding.control_id
                    ));
                }
                let expected_target = format!("{} -> {}", binding.before, binding.after);
                if control.target != expected_target {
                    return Err(format!(
                        "relation {id} edge control {} targets {:?} instead of {:?}",
                        binding.control_id, control.target, expected_target
                    ));
                }
            }
        }
        Ok(())
    }
}

impl MaterializedDacRecord {
    pub fn validate(&self) -> Result<(), String> {
        require_text("record ID", &self.record.id)?;
        require_text("record name", &self.record.name)?;
        require_nonempty("source authorities", &self.record.territory.authorities)?;
        require_texts(
            "included behavior",
            &self.record.territory.included_behavior,
        )?;
        require_texts("territory omissions", &self.record.territory.omissions)?;
        unique_nonempty(
            "source authority ID",
            self.record
                .territory
                .authorities
                .iter()
                .map(|source| source.id.as_str()),
        )?;
        for source in &self.record.territory.authorities {
            require_text("source ID", &source.id)?;
            require_text("source locator", &source.locator)?;
            require_text("source edition", &source.edition)?;
            require_text("source scope", &source.scope)?;
        }
        validate_native_problem(&self.record.native_problem)?;
        require_nonempty("stripped roles", &self.record.stripped_roles)?;
        unique_nonempty(
            "stripped role",
            self.record
                .stripped_roles
                .iter()
                .map(|role| role.role.as_str()),
        )?;
        for role in &self.record.stripped_roles {
            require_text("role domain binding", &role.domain_binding)?;
            require_text("role preserved relation", &role.preserved_relation)?;
        }
        validate_construction(&self.record.construction)?;
        require_nonempty("relies", &self.record.relies)?;
        unique_nonempty("rely", self.record.relies.iter().map(String::as_str))?;
        require_nonempty("controls", &self.record.controls)?;
        unique_nonempty(
            "control ID",
            self.record
                .controls
                .iter()
                .map(|control| control.id.as_str()),
        )?;
        for control in &self.record.controls {
            require_text("control target", &control.target)?;
            require_text("control mutation", &control.mutation)?;
            require_text("control expected failure", &control.expected_failure)?;
            require_texts("control adjacent checks", &control.adjacent_checks)?;
        }
        validate_candidate_control_bindings(&self.record.construction, &self.record.controls)?;
        validate_boundary(&self.record.boundary)?;

        if matches!(self.record.family, ArtifactFamily::CrossExampleRelation) {
            if self.record.oracle.is_some() {
                return Err(
                    "relation records use member oracles, not a relation oracle".to_string()
                );
            }
            validate_relation(
                self.record
                    .relation
                    .as_ref()
                    .ok_or_else(|| "relation record lacks a relation contract".to_string())?,
                &self.record.controls,
            )?;
        } else {
            if self.record.relation.is_some() {
                return Err("non-relation record contains a relation contract".to_string());
            }
            validate_oracle(
                self.record
                    .oracle
                    .as_ref()
                    .ok_or_else(|| "executable result record lacks an oracle".to_string())?,
            )?;
        }

        if let Some(delta) = &self.instance_delta {
            require_text("base evidence identity", &delta.base_evidence_identity)?;
            require_nonempty("assembly seams", &delta.assembly_seams)?;
            if delta.added_relies.is_empty() && delta.replaced_relies.is_empty() {
                return Err(format!("instance {} lacks a rely delta", delta.id));
            }
            for rely in &delta.added_relies {
                require_text("added rely", rely)?;
            }
            unique_nonempty(
                "replaced rely",
                delta
                    .replaced_relies
                    .iter()
                    .map(|replacement| replacement.previous.as_str()),
            )?;
            require_texts(
                "inherited control bindings",
                &delta.inherited_control_bindings,
            )?;
            let controls: BTreeSet<_> = self
                .record
                .controls
                .iter()
                .map(|control| control.id.as_str())
                .collect();
            for binding in &delta.inherited_control_bindings {
                if !controls.contains(binding.as_str()) {
                    return Err(format!(
                        "instance {} binds unknown inherited control {binding}",
                        delta.id
                    ));
                }
            }
        }
        Ok(())
    }
}

fn validate_native_problem(record: &NativeProblemRecord) -> Result<(), String> {
    require_texts("native actors", &record.actors)?;
    require_texts("native state", &record.state)?;
    require_texts("native transitions", &record.transitions)?;
    require_texts("native commitments", &record.commitments)?;
    require_texts("native inputs", &record.inputs)?;
    require_texts("native outputs", &record.outputs)?;
    require_texts("native failures", &record.failures)?;
    require_texts("native obligations", &record.obligations)
}

fn validate_construction(account: &ConstructionAccount) -> Result<(), String> {
    require_nonempty("construction nodes", &account.nodes)?;
    require_nonempty("construction edges", &account.edges)?;
    require_text("execution carrier", &account.execution_carrier)?;
    require_texts("governed commit points", &account.governed_commit_points)?;
    require_texts("permitted host material", &account.permitted_host_material)?;
    unique_nonempty(
        "construction node ID",
        account.nodes.iter().map(|node| node.id.as_str()),
    )?;
    let nodes: BTreeSet<_> = account.nodes.iter().map(|node| node.id.as_str()).collect();
    for node in &account.nodes {
        require_text("implementation identity", &node.implementation_identity)?;
        require_text("construction responsibility", &node.responsibility)?;
    }
    for edge in &account.edges {
        if !nodes.contains(edge.before.as_str()) || !nodes.contains(edge.after.as_str()) {
            return Err(format!(
                "construction edge {} -> {} refers to an unclassified node",
                edge.before, edge.after
            ));
        }
        require_text("construction edge obligation", &edge.obligation)?;
    }
    let new_generic = account
        .nodes
        .iter()
        .any(|node| node.stratum == ConstructionStratum::NewGeneric);
    if account.outcome.supports_reconstruction() && new_generic {
        return Err("catalog composition contains unreviewed new generic code".to_string());
    }
    if account.outcome.is_candidate() {
        if !new_generic {
            return Err(
                "candidate-shape outcome lacks a new-generic construction node".to_string(),
            );
        }
        require_texts("candidate scope delta", &account.scope_delta)?;
        let assessment = account
            .candidate_assessment
            .as_ref()
            .ok_or_else(|| "candidate-shape outcome lacks an assessment".to_string())?;
        require_text(
            "candidate reusable obligation",
            &assessment.reusable_obligation,
        )?;
        require_texts(
            "candidate failed catalog bindings",
            &assessment.failed_catalog_bindings,
        )?;
        require_nonempty("candidate control bindings", &assessment.control_bindings)?;
        let generic_nodes: BTreeSet<_> = account
            .nodes
            .iter()
            .filter(|node| node.stratum == ConstructionStratum::NewGeneric)
            .map(|node| node.id.as_str())
            .collect();
        let bound_nodes: BTreeSet<_> = assessment
            .control_bindings
            .iter()
            .map(|binding| binding.node_id.as_str())
            .collect();
        if generic_nodes != bound_nodes {
            return Err(
                "candidate controls do not bind every new-generic node and only those nodes"
                    .to_string(),
            );
        }
        unique_nonempty(
            "candidate control ID",
            assessment
                .control_bindings
                .iter()
                .map(|binding| binding.control_id.as_str()),
        )?;
        if account.outcome == ConstructionOutcome::UnidentifiedShapeCandidate
            && assessment.abstraction_layer.is_some()
        {
            return Err(
                "unidentified-shape candidate cannot declare an abstraction layer".to_string(),
            );
        }
        if account.outcome == ConstructionOutcome::AbstractionLayerLocalShapeCandidate {
            require_text(
                "candidate abstraction layer",
                assessment.abstraction_layer.as_deref().unwrap_or_default(),
            )?;
            require_texts(
                "candidate failed cross-layer substitutions",
                &assessment.failed_cross_layer_substitutions,
            )?;
        }
    } else if account.candidate_assessment.is_some() {
        return Err("non-candidate outcome contains a candidate assessment".to_string());
    }
    if !account.outcome.supports_reconstruction() {
        require_texts("non-accepting scope delta", &account.scope_delta)?;
    }
    Ok(())
}

fn validate_candidate_control_bindings(
    account: &ConstructionAccount,
    controls: &[ControlRecord],
) -> Result<(), String> {
    let Some(assessment) = &account.candidate_assessment else {
        return Ok(());
    };
    for binding in &assessment.control_bindings {
        let control = controls
            .iter()
            .find(|control| control.id == binding.control_id)
            .ok_or_else(|| {
                format!(
                    "candidate assessment binds unknown control {}",
                    binding.control_id
                )
            })?;
        if control.class != ControlClass::Construction {
            return Err(format!(
                "candidate control {} is not a construction control",
                binding.control_id
            ));
        }
        if control.target != binding.node_id {
            return Err(format!(
                "candidate control {} targets {:?} instead of node {:?}",
                binding.control_id, control.target, binding.node_id
            ));
        }
    }
    Ok(())
}

fn validate_oracle(oracle: &OracleRecord) -> Result<(), String> {
    require_text("oracle ID", &oracle.id)?;
    require_text("oracle method", &oracle.method)?;
    require_text(
        "oracle implementation identity",
        &oracle.implementation_identity,
    )?;
    require_texts("oracle expected data", &oracle.expected_data)?;
    require_text("oracle equivalence relation", &oracle.equivalence_relation)?;
    require_texts("oracle common-mode risks", &oracle.common_mode_risks)?;
    if oracle.imports_shared_structures || oracle.calls_construction_helpers {
        return Err("oracle is not independent of the construction path".to_string());
    }
    Ok(())
}

fn validate_relation(
    relation: &RelationContract,
    controls: &[ControlRecord],
) -> Result<(), String> {
    if relation.assurance_class == RelationAssuranceClass::VocabularyResemblance {
        return Err("vocabulary resemblance cannot accept a relation record".to_string());
    }
    require_texts("relation members", &relation.members)?;
    require_texts("relation shared nodes", &relation.shared_nodes)?;
    require_nonempty("relation shared edges", &relation.shared_edges)?;
    require_texts("relation controls", &relation.relation_control_ids)?;
    require_nonempty(
        "relation member edge controls",
        &relation.member_edge_controls,
    )?;
    unique_nonempty(
        "relation member",
        relation.members.iter().map(String::as_str),
    )?;
    unique_nonempty(
        "relation shared node",
        relation.shared_nodes.iter().map(String::as_str),
    )?;
    let shared_nodes: BTreeSet<_> = relation.shared_nodes.iter().map(String::as_str).collect();
    for edge in &relation.shared_edges {
        if !shared_nodes.contains(edge.before.as_str())
            || !shared_nodes.contains(edge.after.as_str())
        {
            return Err(format!(
                "relation shared edge {} -> {} leaves the shared node set",
                edge.before, edge.after
            ));
        }
    }
    unique_nonempty(
        "relation control ID",
        relation.relation_control_ids.iter().map(String::as_str),
    )?;
    if relation.assurance_class == RelationAssuranceClass::SharedExecutableSubgraph {
        let expected: BTreeSet<_> = relation
            .members
            .iter()
            .flat_map(|member| {
                relation
                    .shared_nodes
                    .iter()
                    .map(move |node| (member.as_str(), node.as_str()))
            })
            .collect();
        let observed: BTreeSet<_> = relation
            .implementation_bindings
            .iter()
            .map(|binding| (binding.member_id.as_str(), binding.node_id.as_str()))
            .collect();
        if observed != expected || relation.implementation_bindings.len() != expected.len() {
            return Err(
                "shared-executable relation lacks an exact member-node binding".to_string(),
            );
        }
        for node in &relation.shared_nodes {
            let identities: BTreeSet<_> = relation
                .implementation_bindings
                .iter()
                .filter(|binding| &binding.node_id == node)
                .map(|binding| binding.implementation_identity.as_str())
                .collect();
            if identities.len() != 1 || identities.contains("") {
                return Err(format!(
                    "shared node {node} does not resolve to one implementation identity"
                ));
            }
        }
        for binding in &relation.implementation_bindings {
            require_text("relation claim path", &binding.claim_path)?;
        }
        let expected_controls: BTreeSet<_> = relation
            .members
            .iter()
            .flat_map(|member| {
                relation
                    .shared_edges
                    .iter()
                    .map(move |edge| (member.as_str(), edge.before.as_str(), edge.after.as_str()))
            })
            .collect();
        let observed_controls: BTreeSet<_> = relation
            .member_edge_controls
            .iter()
            .map(|binding| {
                (
                    binding.member_id.as_str(),
                    binding.before.as_str(),
                    binding.after.as_str(),
                )
            })
            .collect();
        if observed_controls != expected_controls
            || relation.member_edge_controls.len() != expected_controls.len()
        {
            return Err(
                "shared-executable relation lacks an exact member-edge control binding".to_string(),
            );
        }
    }
    let relation_controls: BTreeSet<_> = controls
        .iter()
        .filter(|control| control.class == ControlClass::Relation)
        .map(|control| control.id.as_str())
        .collect();
    for control in &relation.relation_control_ids {
        if !relation_controls.contains(control.as_str()) {
            return Err(format!("relation binds missing relation control {control}"));
        }
    }
    for edge in &relation.shared_edges {
        if !relation
            .member_edge_controls
            .iter()
            .any(|binding| binding.before == edge.before && binding.after == edge.after)
        {
            return Err(format!(
                "relation edge {} -> {} lacks a member control",
                edge.before, edge.after
            ));
        }
    }
    Ok(())
}

fn validate_boundary(boundary: &ClaimBoundary) -> Result<(), String> {
    require_text("claim", &boundary.claim)?;
    require_text("claim ceiling", &boundary.claim_ceiling)?;
    require_texts("residuals", &boundary.residuals)?;
    require_texts("falsifiers", &boundary.falsifiers)
}

fn require_text(label: &str, value: &str) -> Result<(), String> {
    if value.trim().is_empty() {
        Err(format!("{label} is empty"))
    } else {
        Ok(())
    }
}

fn require_nonempty<T>(label: &str, values: &[T]) -> Result<(), String> {
    if values.is_empty() {
        Err(format!("{label} is empty"))
    } else {
        Ok(())
    }
}

fn require_texts(label: &str, values: &[String]) -> Result<(), String> {
    require_nonempty(label, values)?;
    for value in values {
        require_text(label, value)?;
    }
    Ok(())
}

fn unique_nonempty<'a>(
    label: &str,
    values: impl IntoIterator<Item = &'a str>,
) -> Result<(), String> {
    let mut observed = BTreeSet::new();
    for value in values {
        if value.trim().is_empty() || !observed.insert(value) {
            return Err(format!("{label} {value:?} is empty or duplicated"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(id: &str, stratum: ConstructionStratum) -> ConstructionNode {
        ConstructionNode {
            id: id.to_string(),
            stratum,
            implementation_identity: format!("crate::{id}"),
            responsibility: "test responsibility".to_string(),
        }
    }

    #[test]
    fn accepted_composition_rejects_unreviewed_generic_code() {
        let account = ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes: vec![
                node("known", ConstructionStratum::Catalog),
                node("unknown", ConstructionStratum::NewGeneric),
            ],
            edges: vec![ConstructionEdge {
                before: "known".to_string(),
                after: "unknown".to_string(),
                obligation: "ordered".to_string(),
            }],
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: vec!["unknown".to_string()],
            permitted_host_material: vec!["Vec".to_string()],
            scope_delta: Vec::new(),
            candidate_assessment: None,
        };
        assert!(validate_construction(&account)
            .expect_err("new generic code must fail an accepted reconstruction")
            .contains("unreviewed new generic code"));
    }

    #[test]
    fn candidate_outcome_requires_scope_delta_and_generic_node() {
        let account = ConstructionAccount {
            outcome: ConstructionOutcome::AbstractionLayerLocalShapeCandidate,
            nodes: vec![node("known", ConstructionStratum::Catalog)],
            edges: vec![ConstructionEdge {
                before: "known".to_string(),
                after: "known".to_string(),
                obligation: "repeat".to_string(),
            }],
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: vec!["known".to_string()],
            permitted_host_material: vec!["Vec".to_string()],
            scope_delta: vec!["layer boundary".to_string()],
            candidate_assessment: None,
        };
        assert!(validate_construction(&account)
            .expect_err("candidate without generic node must fail")
            .contains("new-generic"));
    }

    #[test]
    fn unidentified_candidate_preserves_a_supported_result() {
        let account = ConstructionAccount {
            outcome: ConstructionOutcome::UnidentifiedShapeCandidate,
            nodes: vec![
                node("known", ConstructionStratum::Catalog),
                node("candidate", ConstructionStratum::NewGeneric),
            ],
            edges: vec![ConstructionEdge {
                before: "known".to_string(),
                after: "candidate".to_string(),
                obligation: "candidate edge".to_string(),
            }],
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: vec!["candidate".to_string()],
            permitted_host_material: vec!["Vec".to_string()],
            scope_delta: vec!["unclassified reusable obligation".to_string()],
            candidate_assessment: Some(CandidateShapeAssessment {
                abstraction_layer: None,
                reusable_obligation: "Preserve the candidate obligation.".to_string(),
                failed_catalog_bindings: vec!["KnownStructure lacks the obligation.".to_string()],
                failed_cross_layer_substitutions: Vec::new(),
                control_bindings: vec![CandidateControlBinding {
                    control_id: "candidate-control".to_string(),
                    node_id: "candidate".to_string(),
                }],
            }),
        };
        validate_construction(&account).expect("supported unidentified candidate");
        assert!(!account.outcome.supports_reconstruction());
    }

    #[test]
    fn layer_local_candidate_requires_cross_layer_evidence() {
        let account = ConstructionAccount {
            outcome: ConstructionOutcome::AbstractionLayerLocalShapeCandidate,
            nodes: vec![
                node("known", ConstructionStratum::Catalog),
                node("candidate", ConstructionStratum::NewGeneric),
            ],
            edges: vec![ConstructionEdge {
                before: "known".to_string(),
                after: "candidate".to_string(),
                obligation: "candidate edge".to_string(),
            }],
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: vec!["candidate".to_string()],
            permitted_host_material: vec!["Vec".to_string()],
            scope_delta: vec!["algorithm layer".to_string()],
            candidate_assessment: Some(CandidateShapeAssessment {
                abstraction_layer: Some("algorithm".to_string()),
                reusable_obligation: "Preserve the layer-local obligation.".to_string(),
                failed_catalog_bindings: vec!["KnownStructure lacks the obligation.".to_string()],
                failed_cross_layer_substitutions: Vec::new(),
                control_bindings: vec![CandidateControlBinding {
                    control_id: "candidate-control".to_string(),
                    node_id: "candidate".to_string(),
                }],
            }),
        };
        assert!(validate_construction(&account)
            .expect_err("layer-local candidate needs failed substitutions")
            .contains("cross-layer substitutions"));
    }

    #[test]
    fn unidentified_candidate_rejects_a_layer_claim() {
        let account = ConstructionAccount {
            outcome: ConstructionOutcome::UnidentifiedShapeCandidate,
            nodes: vec![node("candidate", ConstructionStratum::NewGeneric)],
            edges: vec![ConstructionEdge {
                before: "candidate".to_string(),
                after: "candidate".to_string(),
                obligation: "candidate edge".to_string(),
            }],
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: vec!["candidate".to_string()],
            permitted_host_material: vec!["Vec".to_string()],
            scope_delta: vec!["unclassified obligation".to_string()],
            candidate_assessment: Some(CandidateShapeAssessment {
                abstraction_layer: Some("algorithm".to_string()),
                reusable_obligation: "Preserve the candidate obligation.".to_string(),
                failed_catalog_bindings: vec!["No catalog binding.".to_string()],
                failed_cross_layer_substitutions: Vec::new(),
                control_bindings: vec![CandidateControlBinding {
                    control_id: "candidate-control".to_string(),
                    node_id: "candidate".to_string(),
                }],
            }),
        };
        assert!(validate_construction(&account)
            .expect_err("unidentified candidate must not claim a layer")
            .contains("cannot declare an abstraction layer"));
    }

    #[test]
    fn candidate_control_must_be_a_construction_control() {
        let account = ConstructionAccount {
            outcome: ConstructionOutcome::UnidentifiedShapeCandidate,
            nodes: vec![node("candidate", ConstructionStratum::NewGeneric)],
            edges: vec![ConstructionEdge {
                before: "candidate".to_string(),
                after: "candidate".to_string(),
                obligation: "candidate edge".to_string(),
            }],
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: vec!["candidate".to_string()],
            permitted_host_material: vec!["Vec".to_string()],
            scope_delta: vec!["unclassified obligation".to_string()],
            candidate_assessment: Some(CandidateShapeAssessment {
                abstraction_layer: None,
                reusable_obligation: "Preserve the candidate obligation.".to_string(),
                failed_catalog_bindings: vec!["No catalog binding.".to_string()],
                failed_cross_layer_substitutions: Vec::new(),
                control_bindings: vec![CandidateControlBinding {
                    control_id: "candidate-control".to_string(),
                    node_id: "candidate".to_string(),
                }],
            }),
        };
        let mut controls = vec![ControlRecord {
            id: "candidate-control".to_string(),
            class: ControlClass::Oracle,
            target: "candidate".to_string(),
            mutation: "bypass candidate".to_string(),
            expected_failure: "candidate claim fails".to_string(),
            adjacent_checks: vec!["source result".to_string()],
        }];
        assert!(validate_candidate_control_bindings(&account, &controls)
            .expect_err("candidate needs a construction control")
            .contains("not a construction control"));
        controls[0].class = ControlClass::Construction;
        controls[0].target = "other-node".to_string();
        assert!(validate_candidate_control_bindings(&account, &controls)
            .expect_err("candidate control must target its bound node")
            .contains("instead of node"));
    }

    #[test]
    fn evidence_identity_changes_with_claim_content() {
        let mut record = DacBaseRecord {
            id: "test".to_string(),
            name: "test".to_string(),
            family: ArtifactFamily::DomainPoc,
            evidence_role: EvidenceRole::DomainReconstruction,
            territory: TerritoryRecord {
                authorities: Vec::new(),
                included_behavior: Vec::new(),
                omissions: Vec::new(),
            },
            native_problem: NativeProblemRecord {
                actors: Vec::new(),
                state: Vec::new(),
                transitions: Vec::new(),
                commitments: Vec::new(),
                inputs: Vec::new(),
                outputs: Vec::new(),
                failures: Vec::new(),
                obligations: Vec::new(),
            },
            stripped_roles: Vec::new(),
            construction: ConstructionAccount {
                outcome: ConstructionOutcome::Blocked,
                nodes: Vec::new(),
                edges: Vec::new(),
                execution_carrier: String::new(),
                governed_commit_points: Vec::new(),
                permitted_host_material: Vec::new(),
                scope_delta: Vec::new(),
                candidate_assessment: None,
            },
            relies: Vec::new(),
            oracle: None,
            controls: Vec::new(),
            relation: None,
            boundary: ClaimBoundary {
                claim: "first claim".to_string(),
                claim_ceiling: String::new(),
                residuals: Vec::new(),
                falsifiers: Vec::new(),
            },
        };
        let first = evidence_content_identity(&record).expect("content identity");
        record.boundary.claim = "second claim".to_string();
        let second = evidence_content_identity(&record).expect("content identity");
        assert_ne!(first, second);
        assert!(first.starts_with("sha256:"));
    }
}
