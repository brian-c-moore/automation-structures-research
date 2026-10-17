use formal_example_structures::{
    evidence_content_identity, ArtifactFamily, AuthorityKind, ClaimBoundary, ConstructionAccount,
    ConstructionEdge, ConstructionNode, ConstructionOutcome, ConstructionStratum, ControlClass,
    ControlRecord, DacBaseRecord, EvidenceRegistry, EvidenceRole, InstanceDelta,
    MaterializedDacRecord, MemberEdgeControlBinding, NativeProblemRecord, OracleRecord,
    RecordDefinition, RelationAssuranceClass, RelationContract, SharedImplementationBinding,
    SourceAuthority, StrippedRole, TerritoryRecord,
};

fn s(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_string()).collect()
}

fn source(
    id: &str,
    kind: AuthorityKind,
    locator: &str,
    edition: &str,
    scope: &str,
) -> SourceAuthority {
    SourceAuthority {
        id: id.to_string(),
        kind,
        locator: locator.to_string(),
        edition: edition.to_string(),
        scope: scope.to_string(),
    }
}

fn node(
    id: &str,
    stratum: ConstructionStratum,
    implementation_identity: &str,
    responsibility: &str,
) -> ConstructionNode {
    ConstructionNode {
        id: id.to_string(),
        stratum,
        implementation_identity: implementation_identity.to_string(),
        responsibility: responsibility.to_string(),
    }
}

fn edge(before: &str, after: &str, obligation: &str) -> ConstructionEdge {
    ConstructionEdge {
        before: before.to_string(),
        after: after.to_string(),
        obligation: obligation.to_string(),
    }
}

fn control(
    id: &str,
    class: ControlClass,
    target: &str,
    mutation: &str,
    expected_failure: &str,
    adjacent_checks: &[&str],
) -> ControlRecord {
    ControlRecord {
        id: id.to_string(),
        class,
        target: target.to_string(),
        mutation: mutation.to_string(),
        expected_failure: expected_failure.to_string(),
        adjacent_checks: s(adjacent_checks),
    }
}

fn shared_node(id: &str, implementation_identity: &str, responsibility: &str) -> ConstructionNode {
    node(
        id,
        ConstructionStratum::Catalog,
        implementation_identity,
        responsibility,
    )
}

fn rooted_frontier_nodes() -> Vec<ConstructionNode> {
    vec![
        shared_node(
            "QualityHierarchy",
            "formal-example-structures::quality_hierarchy::QualityHierarchy",
            "Validate and commit the root-relative candidate hierarchy.",
        ),
        shared_node(
            "TraversalEngine",
            "formal-example-structures::traversal::TraversalEngine",
            "Visit admitted work and bind visited-before-accepted progression.",
        ),
        shared_node(
            "CompetitiveSelection",
            "formal-example-structures::selection::CompetitiveSelection",
            "Apply the declared cut policy to unresolved candidates.",
        ),
        shared_node(
            "AllocationSnapshot",
            "formal-example-structures::snapshot::AllocationSnapshot",
            "Commit the selected frontier as one checked result.",
        ),
    ]
}

fn rooted_frontier_edges() -> Vec<ConstructionEdge> {
    vec![
        edge(
            "QualityHierarchy",
            "TraversalEngine",
            "Hierarchy commit precedes completion of candidate discovery.",
        ),
        edge(
            "TraversalEngine",
            "CompetitiveSelection",
            "Candidate discovery completes before the cut policy commits.",
        ),
        edge(
            "CompetitiveSelection",
            "AllocationSnapshot",
            "The cut policy commits before the selected frontier commits.",
        ),
    ]
}

fn neutral_roles(lod: bool) -> Vec<StrippedRole> {
    let bindings = if lod {
        [
            ("context", "observation state and byte capacity"),
            ("target", "one relevant spatial object"),
            ("candidate", "one fidelity representation"),
            ("extension", "the next relation in a fidelity ladder"),
            ("measure", "view-weighted utility and byte charge"),
            ("frontier", "unresolved representation candidates"),
            (
                "cut-policy",
                "best feasible collection under aggregate capacity",
            ),
            ("snapshot", "committed representation frontier"),
        ]
    } else {
        [
            ("context", "source vertex and topology version"),
            ("target", "one requested reachable endpoint"),
            ("candidate", "one finite simple path from the source"),
            (
                "extension",
                "one directed edge that does not repeat a vertex",
            ),
            ("measure", "accumulated nonnegative path charge"),
            ("frontier", "unresolved path candidates"),
            (
                "cut-policy",
                "minimum measure per target with ties retained",
            ),
            ("snapshot", "committed route frontier"),
        ]
    };
    bindings
        .into_iter()
        .map(|(role, domain_binding)| StrippedRole {
            role: role.to_string(),
            domain_binding: domain_binding.to_string(),
            preserved_relation: match role {
                "context" => "Freezes the origin and input version for one evaluation.",
                "target" => "Names an endpoint for which the result may require a representative.",
                "candidate" => "Offers one possible representative for a target.",
                "extension" => "Derives another permitted candidate.",
                "measure" => "Orders candidates relative to the frozen context.",
                "frontier" => "Contains candidates whose effect on the result is unresolved.",
                "cut-policy" => "Admits, replaces, retains, or rejects candidates.",
                "snapshot" => "Commits the complete selected frontier.",
                _ => unreachable!("registered neutral role"),
            }
            .to_string(),
        })
        .collect()
}

fn lod_record() -> DacBaseRecord {
    let mut nodes = rooted_frontier_nodes();
    nodes.extend([
        shared_node(
            "Budget<Bytes>",
            "formal-example-structures::budget::Budget<Bytes>",
            "Reject a candidate plan whose aggregate byte charge exceeds capacity.",
        ),
        node(
            "lod-candidate-derivation",
            ConstructionStratum::Domain,
            "formal-example-domains::lod::{hierarchy_nodes,frontier_targets}",
            "Derive fidelity candidates and their view-weighted utility and byte charge.",
        ),
        node(
            "lod-plan-policy",
            ConstructionStratum::Domain,
            "formal-example-domains::lod::plan_rank",
            "Order complete feasible plans by utility, byte charge, and stable identity.",
        ),
        node(
            "lod-output-projection",
            ConstructionStratum::Connective,
            "formal-example-domains::lod::output_from_choices",
            "Sort selected records and project accumulated totals into the public result.",
        ),
        node(
            "sequential-host",
            ConstructionStratum::Runtime,
            "Rust::Vec+BTreeSet+checked-u64",
            "Provide finite storage, stable identity order, and checked integer operations.",
        ),
    ]);
    let mut edges = rooted_frontier_edges();
    edges.extend([
        edge(
            "sequential-host",
            "lod-candidate-derivation",
            "The finite input is validated before candidate derivation.",
        ),
        edge(
            "lod-candidate-derivation",
            "QualityHierarchy",
            "Every candidate resolves to one reached hierarchy node.",
        ),
        edge(
            "QualityHierarchy",
            "Budget<Bytes>",
            "Capacity is initialized after the candidate hierarchy commits.",
        ),
        edge(
            "Budget<Bytes>",
            "TraversalEngine",
            "Candidate-plan traversal carries the checked remaining capacity.",
        ),
        edge(
            "TraversalEngine",
            "lod-plan-policy",
            "Only complete traversed plans enter the domain ordering function.",
        ),
        edge(
            "AllocationSnapshot",
            "lod-output-projection",
            "Only committed allocation records enter the result projection.",
        ),
    ]);
    DacBaseRecord {
        id: "FEX-DOM-REN-03".to_string(),
        name: "Level of detail".to_string(),
        family: ArtifactFamily::DomainExample,
        evidence_role: EvidenceRole::DomainReconstruction,
        territory: TerritoryRecord {
            authorities: vec![
                source(
                    "FEX-SRC-FUNKHOUSER-1993",
                    AuthorityKind::PrimaryPaper,
                    "https://www.cs.princeton.edu/~funk/sig93.pdf",
                    "Proceedings of SIGGRAPH 93, pages 247-254, August 1993",
                    "Primary source for per-object LOD selection as constrained benefit maximization under a rendering-cost bound; not an authority for this example's byte unit or excluded renderer behavior.",
                ),
                source(
                    "FEX-SRC-LOD-PROBLEM",
                    AuthorityKind::ProblemContract,
                    "formal/examples/domains/rendering/README.md",
                    "formal-examples-manifest-v1",
                    "Finite fidelity ladders, view weights, byte capacity, result order, and exclusions.",
                ),
                source(
                    "FEX-SRC-THEORY-DAC",
                    AuthorityKind::ProjectDecomposition,
                    "docs/domain-abstraction-collapse.md Sections 2.5 and 8.1",
                    "repository publication edition",
                    "Project decomposition donor for the LOD recipe and neutral roles; not an external rendering conformance source.",
                ),
            ],
            included_behavior: s(&[
                "Select at most one supplied fidelity level per finite object.",
                "Maximize total view-weighted utility within one byte capacity.",
                "Break equal utility by lower byte charge and stable ordered choices.",
            ]),
            omissions: s(&[
                "Visibility determination and renderer integration.",
                "Asset streaming, hysteresis, frame timing, and visual-quality claims.",
            ]),
        },
        native_problem: NativeProblemRecord {
            actors: s(&["observer", "renderable object", "fidelity representation"]),
            state: s(&["view weight", "quality ladder", "byte capacity"]),
            transitions: s(&[
                "derive representation candidates",
                "enumerate feasible selections",
                "replace the incumbent with a better feasible selection",
            ]),
            commitments: s(&["one selected representation frontier"]),
            inputs: s(&["finite objects and levels", "view weights", "byte budget"]),
            outputs: s(&["selected object-level pairs", "total bytes and utility"]),
            failures: s(&[
                "invalid or duplicate identities",
                "arithmetic overflow",
                "selected bytes exceed capacity",
                "construction differs from the independent selector",
            ]),
            obligations: s(&[
                "hierarchy validity",
                "capacity preservation",
                "complete deterministic plan ordering",
                "oracle agreement",
            ]),
        },
        stripped_roles: neutral_roles(true),
        construction: ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes,
            edges,
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: s(&[
                "QualityHierarchy.Commit",
                "CompetitiveSelection.Commit",
                "AllocationSnapshot.Commit",
            ]),
            permitted_host_material: s(&[
                "Vec for finite records",
                "BTreeSet for stable identity checks",
                "checked u64 and u128 arithmetic",
                "pure sorting and projection",
            ]),
            scope_delta: Vec::new(),
            candidate_assessment: None,
        },
        relies: s(&[
            "Fidelity ladders are finite and acyclic.",
            "Byte costs are nonnegative integers.",
            "View scoring is pure for the frozen input.",
            "Identity order is deterministic.",
        ]),
        oracle: Some(OracleRecord {
            id: "FEX-REF-LOD-EXHAUSTIVE".to_string(),
            method: "Direct recursive subset enumeration with an independently written comparison rule."
                .to_string(),
            implementation_identity: "formal-example-domains::references::lod_reference"
                .to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "four named fixtures",
                "64 deterministic generated finite inputs",
            ]),
            equivalence_relation: "Exact equality of selected records, total bytes, and total utility."
                .to_string(),
            common_mode_risks: s(&[
                "Both paths interpret the same view-weighted utility definition.",
                "Both paths use the same public input and output data types.",
            ]),
        }),
        controls: vec![
            control(
                "FEX-CTRL-LOD-DISCOVERY-BYPASS",
                ControlClass::Construction,
                "QualityHierarchy -> TraversalEngine",
                "Bypass hierarchy-backed discovery and pass supplied targets directly to plan traversal.",
                "recipe-binding fails while the independent result and capacity check remain green.",
                &["independent-result", "budget-consistency"],
            ),
            control(
                "FEX-CTRL-LOD-SELECTION-BYPASS",
                ControlClass::Construction,
                "TraversalEngine -> CompetitiveSelection",
                "Commit the first complete feasible plan without invoking competitive selection.",
                "recipe-binding or independent-result fails while hierarchy and capacity checks remain active.",
                &["hierarchy-obligations", "budget-consistency"],
            ),
            control(
                "FEX-CTRL-LOD-BUDGET-CHARGE",
                ControlClass::Construction,
                "Budget<Bytes> charge and snapshot capacity seam",
                "Skip capacity charges during candidate-plan enumeration.",
                "The allocation snapshot rejects the over-capacity selection.",
                &["independent result remains available", "hierarchy validation remains green"],
            ),
            control(
                "FEX-CTRL-LOD-SNAPSHOT-TRACE",
                ControlClass::Construction,
                "CompetitiveSelection -> AllocationSnapshot",
                "Commit the snapshot through a detached trace.",
                "recipe-binding fails while the selected domain result still equals the oracle.",
                &["independent-result", "budget-consistency"],
            ),
        ],
        relation: None,
        boundary: ClaimBoundary {
            claim: "A bounded level-of-detail scenario uses the capacity-bounded rooted-frontier composition and agrees with a separate exhaustive result."
                .to_string(),
            claim_ceiling: "Bounded executable construction evidence for finite supplied quality ladders and byte budgets."
                .to_string(),
            residuals: s(&[
                "No renderer, visibility system, streaming system, or GPU integration is claimed.",
                "View scoring and fidelity utility remain domain functions.",
                "Temporal hysteresis and performance claims are excluded.",
            ]),
            falsifiers: s(&[
                "Any accepted input differs from the independent exhaustive result.",
                "Any committed selection exceeds capacity.",
                "A registered structure edge can be bypassed without failing its binding check.",
                "Unclassified reusable generic behavior appears on the claim path.",
            ]),
        },
    }
}

fn lod_assembly_delta() -> InstanceDelta {
    let base_evidence_identity =
        evidence_content_identity(&lod_record()).expect("LOD evidence record serializes");
    InstanceDelta {
        id: "FEX-ASM-01".to_string(),
        name: "LOD/quality scaling".to_string(),
        family: ArtifactFamily::IntegratedReconstruction,
        evidence_role: EvidenceRole::SourceReconstruction,
        base_id: "FEX-DOM-REN-03".to_string(),
        base_evidence_identity,
        territory: None,
        native_problem: None,
        stripped_roles: None,
        added_nodes: vec![node(
            "assembly-report",
            ConstructionStratum::Connective,
            "formal-example-domains::lod::{scenarios,assembly_claim}",
            "Bind the scenario set and inherited checks into one assembly result.",
        )],
        assembly_seams: vec![edge(
            "AllocationSnapshot",
            "assembly-report",
            "Every assembly scenario reports a committed result with all inherited checks green.",
        )],
        added_relies: s(&["Every registered LOD scenario remains present in the assembly set."]),
        replaced_relies: Vec::new(),
        inherited_control_bindings: s(&[
            "FEX-CTRL-LOD-DISCOVERY-BYPASS",
            "FEX-CTRL-LOD-SELECTION-BYPASS",
            "FEX-CTRL-LOD-BUDGET-CHARGE",
            "FEX-CTRL-LOD-SNAPSHOT-TRACE",
        ]),
        added_controls: Vec::new(),
        oracle: Some(OracleRecord {
            id: "FEX-REF-LOD-ASSEMBLY-EXHAUSTIVE".to_string(),
            method: "Apply the separate exhaustive LOD reference to a unique named scenario set and compare the complete name-to-result relation."
                .to_string(),
            implementation_identity:
                "formal-example-domains::references::lod_assembly_reference".to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "full-budget scenario",
                "budget-cut scenario",
                "zero-budget scenario",
                "view-change scenario",
            ]),
            equivalence_relation:
                "Exact equality of the sorted scenario-name and LOD-output pairs.".to_string(),
            common_mode_risks: s(&[
                "The assembly and reference share the public scenario input types.",
                "The assembly reference reuses the independent per-scenario exhaustive oracle.",
            ]),
        }),
        boundary: ClaimBoundary {
            claim: "The LOD quality-scaling reconstruction crosses every declared structural seam and agrees with its domain reference."
                .to_string(),
            claim_ceiling: "Scenario-set assembly evidence over the inherited bounded LOD construction."
                .to_string(),
            residuals: s(&[
                "The assembly inherits the LOD product and performance exclusions.",
                "No rendering engine or asset lifecycle is constructed.",
            ]),
            falsifiers: s(&[
                "A registered scenario is absent.",
                "An inherited control no longer reaches the same construction edge.",
                "An assembly result omits a declared check or evidence identity.",
            ]),
        },
    }
}

fn ospf_record() -> DacBaseRecord {
    let mut nodes = rooted_frontier_nodes();
    nodes.extend([
        shared_node(
            "ResourceRegistry",
            "formal-example-structures::resource_registry::ResourceRegistry",
            "Register normalized topology vertices before graph construction.",
        ),
        shared_node(
            "RelationshipGraph",
            "formal-example-structures::relationship_graph::RelationshipGraph",
            "Commit the directed weighted topology used by both route constructions.",
        ),
        shared_node(
            "Reduction",
            "formal-example-structures::reduction::PathReduction::compare",
            "Record accepted distance improvements in the conventional construction.",
        ),
        node(
            "finite-path-enumeration",
            ConstructionStratum::Domain,
            "formal-example-domains::ospf::enumerate_route_frontier",
            "Enumerate unresolved finite simple-path candidates from the normalized topology.",
        ),
        node(
            "route-projection",
            ConstructionStratum::Domain,
            "formal-example-domains::ospf::{next_hops,project_route}",
            "Accumulate path charge and project equal-minimum first-hop sets.",
        ),
        node(
            "conventional-spf-policy",
            ConstructionStratum::Conventional,
            "formal-example-domains::ospf::{run_ospf_conventional,compute_ospf,commit_conventional}",
            "Retain the conventional Dijkstra-shaped route construction as a separate comparison path.",
        ),
        node(
            "sequential-host",
            ConstructionStratum::Runtime,
            "Rust::Vec+BTreeMap+BTreeSet+checked-u64",
            "Provide finite storage, stable ordering, and checked path-cost arithmetic.",
        ),
    ]);
    let mut edges = rooted_frontier_edges();
    edges.extend([
        edge(
            "ResourceRegistry",
            "RelationshipGraph",
            "Every graph endpoint resolves to one registered vertex.",
        ),
        edge(
            "RelationshipGraph",
            "finite-path-enumeration",
            "Candidate enumeration reads only the committed normalized topology.",
        ),
        edge(
            "finite-path-enumeration",
            "QualityHierarchy",
            "Every unresolved path candidate resolves to one hierarchy node.",
        ),
        edge(
            "CompetitiveSelection",
            "route-projection",
            "Only equal-minimum selected candidates enter route projection.",
        ),
        edge(
            "RelationshipGraph",
            "conventional-spf-policy",
            "The conventional path reads the same committed topology.",
        ),
        edge(
            "conventional-spf-policy",
            "Reduction",
            "Every strict distance improvement records one reduction relaxation.",
        ),
        edge(
            "Reduction",
            "AllocationSnapshot",
            "The conventional route set commits after reduction completes.",
        ),
        edge(
            "sequential-host",
            "ResourceRegistry",
            "The finite input is validated before topology registration.",
        ),
    ]);
    DacBaseRecord {
        id: "FEX-OSPF-001".to_string(),
        name: "Bounded OSPFv2 intra-area route selection".to_string(),
        family: ArtifactFamily::DomainPoc,
        evidence_role: EvidenceRole::DomainReconstruction,
        territory: TerritoryRecord {
            authorities: vec![
                source(
                    "FEX-SRC-RFC2328",
                    AuthorityKind::NormativeStandard,
                    "https://www.rfc-editor.org/rfc/rfc2328.html",
                    "RFC 2328, April 1998",
                    "Sections 2.1.2, 2.2, 2.4, 11.2, 16.1, 16.1.1, and 16.8 for normalized intra-area route calculation.",
                ),
                source(
                    "FEX-SRC-RFC2328-FIGURE2",
                    AuthorityKind::PublishedFixture,
                    "RFC 2328 Figure 2, Figure 3, Figure 5, and Table 2",
                    "RFC 2328, April 1998",
                    "RT6 normalized topology and all 15 local-destination expected rows.",
                ),
                source(
                    "FEX-SRC-OSPF-PROBLEM",
                    AuthorityKind::ProblemContract,
                    "formal/examples/domains/networking/README.md",
                    "formal-examples-manifest-v1",
                    "Finite normalized input contract, root exclusion rely, construction choices, and exclusions.",
                ),
            ],
            included_behavior: s(&[
                "Compute intra-area minimum path cost for every supplied reachable destination.",
                "Retain the complete equal-cost first-hop set.",
                "Use one finite normalized directed topology version per run.",
            ]),
            omissions: s(&[
                "LSA origination, flooding, database exchange, and adjacency state.",
                "Inter-area and external routes, aging, authentication, convergence, and forwarding installation.",
            ]),
        },
        native_problem: NativeProblemRecord {
            actors: s(&["root router", "topology vertex", "destination endpoint"]),
            state: s(&["topology version", "directed weighted links", "route candidates"]),
            transitions: s(&[
                "extend a candidate through one directed link",
                "accumulate path charge",
                "replace or retain candidates at the current minimum",
            ]),
            commitments: s(&["one complete route snapshot for the supplied destinations"]),
            inputs: s(&[
                "root vertex",
                "typed vertices and directed links",
                "destination set excluding the root",
                "expected topology version",
            ]),
            outputs: s(&["destination cost and equal-cost next-hop set"]),
            failures: s(&[
                "invalid identities or endpoints",
                "stale topology",
                "root appears as a destination",
                "path-cost overflow",
                "construction or fixture disagreement",
            ]),
            obligations: s(&[
                "topology integrity",
                "minimum cost per destination",
                "equal-minimum retention",
                "complete destination coverage",
                "oracle and published-fixture agreement",
            ]),
        },
        stripped_roles: neutral_roles(false),
        construction: ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes,
            edges,
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: s(&[
                "RelationshipGraph.Commit",
                "QualityHierarchy.Commit",
                "CompetitiveSelection.Commit",
                "Reduction.Compare",
                "AllocationSnapshot.Commit",
            ]),
            permitted_host_material: s(&[
                "Vec and ordered maps for finite graph state",
                "checked u64 addition for path cost",
                "stable sorting and set projection",
                "finite simple-path enumeration at the stated bound",
            ]),
            scope_delta: Vec::new(),
            candidate_assessment: None,
        },
        relies: s(&[
            "The normalized graph is finite and has nonnegative finite link costs.",
            "Vertex identities are unique and every link endpoint is registered.",
            "The destination set excludes the root.",
            "The fixture supplies the exact expected topology version.",
        ]),
        oracle: Some(OracleRecord {
            id: "FEX-REF-OSPF-BELLMAN-FORD".to_string(),
            method: "Bellman-Ford distance relaxation with separate predecessor first-hop projection."
                .to_string(),
            implementation_identity: "formal-example-domains::references::ospf_reference"
                .to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "five named finite topology scenarios",
                "96 deterministic generated topologies",
                "RFC 2328 RT6 Table 2 rows",
            ]),
            equivalence_relation: "Exact equality of destination identities, minimum costs, and ordered equal-cost next-hop sets."
                .to_string(),
            common_mode_risks: s(&[
                "The reference and conventional path share the normalized input interpretation.",
                "Equal-cost first-hop propagation has similar domain rules in both implementations.",
            ]),
        }),
        controls: vec![
            control(
                "FEX-CTRL-OSPF-LINK-COST",
                ControlClass::SourceInput,
                "normalized link cost",
                "Increase the first registered link cost.",
                "The route result changes while both construction paths still agree with the reference for the mutated input.",
                &["topology integrity", "construction agreement"],
            ),
            control(
                "FEX-CTRL-OSPF-DIRECTION",
                ControlClass::SourceInput,
                "directed topology relation",
                "Reverse the first registered directed link.",
                "The input or destination-coverage obligation rejects the changed relation.",
                &["identity validation", "freshness validation"],
            ),
            control(
                "FEX-CTRL-OSPF-FRESHNESS",
                ControlClass::Rely,
                "topology version rely",
                "Supply a stale topology version.",
                "Both construction paths reject the stale input before route commitment.",
                &["identity validation", "root exclusion"],
            ),
            control(
                "FEX-CTRL-OSPF-CONVENTIONAL-COVERAGE",
                ControlClass::ConventionalPath,
                "conventional destination coverage",
                "Drop the last destination during conventional commitment.",
                "The conventional coverage check fails without implicating rooted-frontier selection.",
                &["rooted-frontier oracle agreement", "shared relation input"],
            ),
            control(
                "FEX-CTRL-OSPF-HIERARCHY",
                ControlClass::Construction,
                "finite-path-enumeration -> QualityHierarchy",
                "Corrupt one frontier parent relation.",
                "Hierarchy validation rejects the rooted-frontier construction.",
                &["conventional oracle agreement", "source topology integrity"],
            ),
            control(
                "FEX-CTRL-OSPF-DISCOVERY-BYPASS",
                ControlClass::Construction,
                "QualityHierarchy -> TraversalEngine",
                "Submit generated targets without shared hierarchy discovery.",
                "recipe-binding fails because shared discovery no longer crosses the registered edge.",
                &["conventional oracle agreement", "rooted-frontier independent result"],
            ),
            control(
                "FEX-CTRL-OSPF-SELECTION-BYPASS",
                ControlClass::Construction,
                "TraversalEngine -> CompetitiveSelection",
                "Choose the first candidate per target without shared competitive selection.",
                "recipe-binding fails and any wrong route result is rejected by the independent reference.",
                &["conventional oracle agreement", "candidate-input identity"],
            ),
            control(
                "FEX-CTRL-OSPF-SNAPSHOT",
                ControlClass::Construction,
                "CompetitiveSelection -> AllocationSnapshot",
                "Commit the rooted-frontier snapshot through a detached trace.",
                "recipe-binding fails while both route results remain correct.",
                &["conventional agreement", "rooted-frontier independent result"],
            ),
            control(
                "FEX-CTRL-OSPF-PRESELECTED",
                ControlClass::Construction,
                "unresolved candidate boundary",
                "Replace the enumerated candidate set with conventional winners before shared selection.",
                "The candidate-identity control fails even though the final routes remain correct.",
                &["conventional oracle agreement", "rooted-frontier result agreement"],
            ),
        ],
        relation: None,
        boundary: ClaimBoundary {
            claim: "For normalized finite link-state inputs, conventional Dijkstra and rooted-frontier selection compute the same route costs and equal-cost next-hop sets as a separate Bellman-Ford reference."
                .to_string(),
            claim_ceiling: "Bounded executable intra-area route-selection evidence over normalized finite topologies."
                .to_string(),
            residuals: s(&[
                "This is not an OSPF protocol implementation.",
                "The input is normalized rather than decoded from live LSAs.",
                "The rooted-frontier path enumerates finite simple paths and makes no routing-performance claim.",
                "Protocol exchange, inter-area behavior, convergence, and deployment remain excluded.",
            ]),
            falsifiers: s(&[
                "Either construction disagrees with the Bellman-Ford reference on an accepted input.",
                "The RT6 result differs from any registered RFC 2328 Table 2 row.",
                "A root destination is accepted.",
                "The rooted-frontier path consumes preselected conventional winners without detection.",
                "A registered construction edge can be bypassed while binding remains green.",
            ]),
        },
    }
}

fn edf_record() -> DacBaseRecord {
    let nodes = vec![
        node(
            "checked-host",
            ConstructionStratum::Runtime,
            "core::checked-arithmetic-and-owned-collections",
            "Carry finite task, release, job, and trace values without owning a scheduling obligation.",
        ),
        node(
            "task-contract",
            ConstructionStratum::Domain,
            "formal-example-domains::edf::TaskSpec",
            "Bind task identity, execution demand, relative deadline, and minimum release separation.",
        ),
        node(
            "processor-demand-projection",
            ConstructionStratum::Domain,
            "formal-example-domains::edf::interval_demand",
            "Project repeating and finite-interval processor demand from the admitted task contract.",
        ),
        shared_node(
            "Budget",
            "formal-example-structures::budget::Budget<ExecutionTicks>",
            "Reject capacity overdraw during admission and serve as the sole per-job progress authority.",
        ),
        shared_node(
            "ResourceRegistry",
            "formal-example-structures::resource_registry::ResourceRegistry<TaskSpec>",
            "Publish exactly the task set whose admission charges accepted.",
        ),
        node(
            "release-and-readiness-projection",
            ConstructionStratum::Domain,
            "formal-example-domains::edf::{periodic_release_trace, expected_ready_resources}",
            "Derive released unfinished work and independently reconstruct the complete ready set.",
        ),
        shared_node(
            "Sequential",
            "formal-example-structures::sequential::Sequential<Option<usize>>",
            "Order one begin and one completion record for every execution quantum.",
        ),
        shared_node(
            "CompetitiveSelection",
            "formal-example-structures::selection::CompetitiveSelection::select_min_index",
            "Select the least urgency key from the complete ready set.",
        ),
        node(
            "SelectThenActuate",
            ConstructionStratum::Connective,
            "formal-example-structures::select_then_actuate::SelectThenActuate::select_min_and_actuate",
            "Bind the selected resource to the resource passed into the effect closure.",
        ),
        shared_node(
            "ActuationPass",
            "formal-example-structures::actuation::ActuationPass",
            "Record one selected-resource effect in the current quantum.",
        ),
        node(
            "deadline-verifier",
            ConstructionStratum::Domain,
            "formal-example-domains::edf::{record_misses, verify_positive_recipe}",
            "Reject incomplete work at its absolute deadline and reconcile every structural premise.",
        ),
    ];
    let edges = vec![
        edge(
            "checked-host",
            "task-contract",
            "Checked finite values enter source-model validation before scheduling work begins.",
        ),
        edge(
            "task-contract",
            "processor-demand-projection",
            "Only validated task parameters enter demand projection.",
        ),
        edge(
            "processor-demand-projection",
            "Budget",
            "Every repeating and finite-interval demand value is charged to its matching capacity.",
        ),
        edge(
            "Budget",
            "ResourceRegistry",
            "The authoritative task set publishes only after every required admission charge accepts.",
        ),
        edge(
            "ResourceRegistry",
            "release-and-readiness-projection",
            "Release generation and readiness read the admitted task identities and parameters.",
        ),
        edge(
            "release-and-readiness-projection",
            "Sequential",
            "Each time position begins after releases are incorporated and before selection.",
        ),
        edge(
            "Sequential",
            "CompetitiveSelection",
            "The current quantum begins before its complete ready set is ranked.",
        ),
        edge(
            "CompetitiveSelection",
            "SelectThenActuate",
            "The minimum urgency winner enters the shared selection-effect handoff.",
        ),
        edge(
            "SelectThenActuate",
            "ActuationPass",
            "The handoff derives the effect target from the selected resource.",
        ),
        edge(
            "ActuationPass",
            "Budget",
            "The selected job effect performs exactly one unit of authoritative progress.",
        ),
        edge(
            "Budget",
            "Sequential",
            "The quantum completes only after the progress charge commits.",
        ),
        edge(
            "Sequential",
            "deadline-verifier",
            "Completed quantum history and job accounting enter the deadline verdict.",
        ),
    ];
    DacBaseRecord {
        id: "FEX-DOM-RT-01".to_string(),
        name: "Preemptive earliest-deadline-first scheduling".to_string(),
        family: ArtifactFamily::DomainExample,
        evidence_role: EvidenceRole::DomainReconstruction,
        territory: TerritoryRecord {
            authorities: vec![
                source(
                    "FEX-SRC-EDF-PROBLEM",
                    AuthorityKind::ProblemContract,
                    "formal/examples/case-studies/preemptive-edf/README.md",
                    "formal-examples-manifest-v1",
                    "Preemptive uniprocessor task contract, construction boundary, relies, controls, and exclusions.",
                ),
                source(
                    "FEX-SRC-LIU-LAYLAND-1973",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1145/321738.321743",
                    "Journal of the ACM 20(1), 1973",
                    "Periodic hard-real-time task model and deadline-driven uniprocessor scheduling result.",
                ),
                source(
                    "FEX-SRC-BARUAH-ROSIER-HOWELL-1990",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1007/BF01995675",
                    "Real-Time Systems 2, 1990",
                    "Finite processor-demand feasibility test for integer-time periodic tasks.",
                ),
                source(
                    "FEX-SRC-BARUAH-MOK-ROSIER-1990",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1109/REAL.1990.128746",
                    "11th IEEE Real-Time Systems Symposium, 1990",
                    "One-processor sporadic task model and feasibility relation.",
                ),
                source(
                    "FEX-SRC-LINUX-SCHED-DEADLINE",
                    AuthorityKind::ExecutableAuthority,
                    "https://docs.kernel.org/scheduler/sched-deadline.html",
                    "Linux kernel documentation, retrieved 2026-08-26",
                    "Operational interpretation of runtime, deadline, period, admission, and earliest scheduling deadline.",
                ),
            ],
            included_behavior: s(&[
                "Admit synchronous periodic and validated sporadic task sets through repeating and finite-interval processor-demand checks.",
                "At every non-idle quantum, select the earliest absolute deadline from all released unfinished jobs.",
                "Advance exactly one selected job by one execution tick and record ordered completion evidence.",
                "Report unfinished work when its absolute deadline is reached.",
            ]),
            omissions: s(&[
                "Multiprocessor scheduling, shared-lock blocking, non-preemptive sections, and priority inheritance.",
                "Clock error, interrupt cost, context-switch cost, release jitter outside the input trace, and kernel implementation behavior.",
                "Scheduling throughput, latency overhead, memory use, and comparison with specialized implementations.",
            ]),
        },
        native_problem: NativeProblemRecord {
            actors: s(&["task contract", "released job", "single execution resource", "deadline observer"]),
            state: s(&[
                "admitted task registry",
                "released unfinished jobs",
                "per-job remaining execution demand",
                "ordered quantum history",
            ]),
            transitions: s(&[
                "charge repeating and finite-interval demand",
                "publish the admitted task set",
                "release a job after its minimum separation",
                "derive all ready jobs",
                "select the least absolute deadline",
                "apply one unit of progress to the selected job",
                "complete the quantum",
                "record any expired unfinished job",
            ]),
            commitments: s(&[
                "task registry publication after complete admission",
                "one winner-to-effect commit per non-idle quantum",
                "one ordered quantum completion record",
                "deadline verdict over authoritative progress accounting",
            ]),
            inputs: s(&[
                "unique task identity",
                "positive integer execution demand",
                "positive integer relative deadline",
                "positive integer period or minimum release separation",
                "finite execution horizon",
            ]),
            outputs: s(&[
                "admission decision and certificate",
                "ordered dispatch records",
                "completed-job count",
                "deadline-miss records",
                "typed structural trace",
            ]),
            failures: s(&[
                "invalid task or release contract",
                "processor demand exceeds a checked capacity",
                "incomplete ready set",
                "wrong urgency winner",
                "winner and effect target differ",
                "non-unit or missing progress",
                "unfinished work reaches its deadline",
                "recipe evidence is absent or misordered",
            ]),
            obligations: s(&[
                "complete capacity admission",
                "authoritative task identity",
                "complete readiness",
                "earliest-deadline winner",
                "winner-to-effect identity",
                "unit progress accounting",
                "work conservation",
                "sequential quantum order",
                "deadline observation",
            ]),
        },
        stripped_roles: vec![
            StrippedRole {
                role: "identity".to_string(),
                domain_binding: "task and released-job identity".to_string(),
                preserved_relation: "Only admitted identities can produce governed work.".to_string(),
            },
            StrippedRole {
                role: "capacity".to_string(),
                domain_binding: "processor supply over repeating and finite intervals".to_string(),
                preserved_relation: "Projected demand cannot exceed its matching available amount.".to_string(),
            },
            StrippedRole {
                role: "eligibility".to_string(),
                domain_binding: "released unfinished jobs".to_string(),
                preserved_relation: "Every and only currently eligible item enters selection.".to_string(),
            },
            StrippedRole {
                role: "urgency".to_string(),
                domain_binding: "absolute deadline with deterministic ties".to_string(),
                preserved_relation: "The least urgency key wins among all eligible items.".to_string(),
            },
            StrippedRole {
                role: "allocation".to_string(),
                domain_binding: "one selected job resource".to_string(),
                preserved_relation: "At most one eligible resource is selected per position.".to_string(),
            },
            StrippedRole {
                role: "effect".to_string(),
                domain_binding: "one execution debit".to_string(),
                preserved_relation: "The effect target is the selected resource.".to_string(),
            },
            StrippedRole {
                role: "progress".to_string(),
                domain_binding: "remaining execution demand".to_string(),
                preserved_relation: "One governed effect consumes one declared unit.".to_string(),
            },
            StrippedRole {
                role: "order".to_string(),
                domain_binding: "execution quantum position".to_string(),
                preserved_relation: "Begin precedes selection, effect, and completion at every position.".to_string(),
            },
            StrippedRole {
                role: "observation".to_string(),
                domain_binding: "deadline verdict".to_string(),
                preserved_relation: "Expired incomplete work is observable from authoritative state.".to_string(),
            },
        ],
        construction: ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes,
            edges,
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: s(&[
                "Budget.Commit for every admission charge",
                "ResourceRegistry.Commit after complete admission",
                "CompetitiveSelection.Commit for every non-idle quantum",
                "ActuationPass.Commit on the selected resource",
                "Budget.Commit for one execution tick",
                "Sequential.Complete for every quantum",
            ]),
            permitted_host_material: s(&[
                "checked integer arithmetic for domain time and demand values",
                "owned finite collections for tasks, releases, jobs, and traces",
                "stable identity ordering for deterministic ties",
                "finite event generation at the declared execution horizon",
            ]),
            scope_delta: Vec::new(),
            candidate_assessment: None,
        },
        relies: s(&[
            "Execution uses one preemptive processor with one unit of supply per integer time position.",
            "Tasks are independent and do not self-suspend or block on shared resources.",
            "Declared execution demand is an upper bound for each job and task timing parameters are correct.",
            "Scheduling and preemption overhead are outside the time model.",
            "Release and completion observations are atomic at the modeled quantum boundary.",
            "The cited EDF and processor-demand results apply to the declared source model.",
        ]),
        oracle: Some(OracleRecord {
            id: "FEX-REF-EDF-DUAL".to_string(),
            method: "A separately written processor-demand calculation checks admission; a separate exhaustive state search enumerates every eligible per-quantum choice for bounded released-job sets."
                .to_string(),
            implementation_identity: "formal-example-domains::references::edf_reference_bundle"
                .to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "named arbitrary-deadline, interval-overload, urgency-sensitive, and long-run-overload task sets",
                "798 deterministic admission comparisons with 271 admitted full-recipe runs",
                "212 deterministic exhaustive scheduling comparisons",
            ]),
            equivalence_relation: "Exact admission-decision equality and exact equality between bounded exhaustive feasibility and the no-deadline-miss execution verdict."
                .to_string(),
            common_mode_risks: s(&[
                "The construction and separate admission calculation implement the same published processor-demand formula.",
                "All execution paths share the same task and integer-time interpretation.",
                "The exhaustive search and construction use the same finite horizon inclusion rule.",
            ]),
        }),
        controls: vec![
            control(
                "FEX-CTRL-EDF-EARLY-RELEASE",
                ControlClass::SourceInput,
                "task-contract",
                "Release one sporadic job before its declared minimum separation.",
                "Input validation rejects the release trace before execution.",
                &["task identity", "positive timing parameters"],
            ),
            control(
                "FEX-CTRL-EDF-BYPASS-ADMISSION",
                ControlClass::Construction,
                "processor-demand-projection -> Budget",
                "Publish a task set without making its admission charges.",
                "A long-run overload is admitted and misses a deadline; the structural verifier rejects the absent charges.",
                &["separate admission rejection", "deadline observation"],
            ),
            control(
                "FEX-CTRL-EDF-UTILIZATION-ONLY",
                ControlClass::Construction,
                "processor-demand-projection -> Budget",
                "Keep the repeating charge but omit finite-interval checks.",
                "A local interval overload is admitted and misses a deadline; the verifier rejects incomplete interval coverage.",
                &["repeating capacity check", "separate admission rejection"],
            ),
            control(
                "FEX-CTRL-EDF-OMIT-READY",
                ControlClass::Construction,
                "release-and-readiness-projection -> CompetitiveSelection",
                "Remove one eligible job before selection.",
                "Recomputed readiness rejects the candidate set even when all deadlines remain green.",
                &["winner optimality within supplied candidates", "deadline observation"],
            ),
            control(
                "FEX-CTRL-EDF-REVERSE-URGENCY",
                ControlClass::Construction,
                "release-and-readiness-projection -> CompetitiveSelection",
                "Prefer the greatest absolute deadline instead of the least.",
                "A feasible admitted witness misses a deadline.",
                &["complete candidate set", "unit progress"],
            ),
            control(
                "FEX-CTRL-EDF-MISDIRECT-EFFECT",
                ControlClass::Construction,
                "CompetitiveSelection -> SelectThenActuate",
                "Apply the execution effect to a different ready job.",
                "The missing shared handoff rejects the trace even when all deadlines remain green.",
                &["complete candidate set", "unit Budget charge"],
            ),
            control(
                "FEX-CTRL-EDF-SUPPRESS-PROGRESS",
                ControlClass::Construction,
                "ActuationPass -> Budget",
                "Record selection and effect without a progress charge.",
                "Jobs remain incomplete, deadline misses appear, and Budget reconciliation rejects the trace.",
                &["winner-to-effect identity", "sequential completion"],
            ),
            control(
                "FEX-CTRL-EDF-ACCELERATE-PROGRESS",
                ControlClass::Construction,
                "ActuationPass -> Budget",
                "Charge two execution units in one quantum.",
                "Unit-charge and dispatch-to-spend checks reject false early completion while deadlines remain green.",
                &["winner-to-effect identity", "deadline observation"],
            ),
            control(
                "FEX-CTRL-EDF-REPEATED-ORDER",
                ControlClass::Construction,
                "Budget -> Sequential",
                "Reverse a later repeated commit-complete edge after one correct quantum.",
                "Per-quantum evidence accepts the first instance and rejects the later misordered instance.",
                &["unique event identity", "earlier quantum order"],
            ),
        ],
        relation: None,
        boundary: ClaimBoundary {
            claim: "For the registered preemptive uniprocessor task model and bounded cases, the shared-structure construction applies finite processor-demand admission and complete-ready-set earliest-deadline dispatch and agrees with separate admission and exhaustive-scheduling oracles, while the mechanized premise-binding model passes its positive and isolated-control checks."
                .to_string(),
            claim_ceiling: "Bounded executable reconstruction plus bounded model checking for the formal premise-binding model; the unbounded scheduling implication remains a registered reliance on the cited EDF and processor-demand theorems."
                .to_string(),
            residuals: s(&[
                "The Rust differential evidence is bounded to the registered generated grids and named release traces.",
                "The bounded formal model checks composition premises; it does not re-prove the published EDF optimality or processor-demand theorems.",
                "Kernel conformance, multiprocessor behavior, blocking, timing overhead, and performance remain outside the claim.",
            ]),
            falsifiers: s(&[
                "The construction and separate admission calculation disagree on any accepted registered input.",
                "Bounded EDF execution and exhaustive feasibility disagree on any registered finite job set.",
                "Any admitted positive recipe misses a deadline or fails its complete structural verifier.",
                "Any named premise control passes the structural verifier.",
                "The formal premise-binding model fails a declared invariant or a paired control does not violate its target.",
                "A load-bearing source responsibility cannot be assigned to a registered structure, connective, domain function, runtime rely, or explicit residual.",
            ]),
        },
    }
}

fn crdt_record() -> DacBaseRecord {
    let nodes = vec![
        shared_node(
            "ResourceRegistry",
            "formal-example-structures::resource_registry::ResourceRegistry",
            "Register replica, operation, and captured-state identities without replacement.",
        ),
        shared_node(
            "Reduction",
            "formal-example-structures::reduction::Reduction::fold",
            "Fold the exact local and delivered payloads through the registered join function.",
        ),
        shared_node(
            "ActuationPass",
            "formal-example-structures::actuation::ActuationPass",
            "Bind each local edit or delivery effect to its named replica target.",
        ),
        shared_node(
            "Sequential",
            "formal-example-structures::sequential::Sequential",
            "Record the finite edit, capture, and delivery interleaving used by one executable run.",
        ),
        node(
            "json-operation-and-query",
            ConstructionStratum::Domain,
            "formal-example-domains::crdt::{Operation,materialize}",
            "Create source-visible operation contexts and materialize causally maximal JSON scalar values.",
        ),
        node(
            "merge-and-delivery-verifier",
            ConstructionStratum::Domain,
            "formal-example-domains::crdt::verify_run",
            "Check merge premises, exact issued-state coverage, per-delivery recipes, and equal final views.",
        ),
    ];
    let edges = vec![
        edge(
            "ResourceRegistry",
            "Sequential",
            "Only registered replica identities may begin local edits, captures, or deliveries.",
        ),
        edge(
            "Sequential",
            "json-operation-and-query",
            "A local step begins before its source-visible context and operation content are fixed.",
        ),
        edge(
            "json-operation-and-query",
            "ResourceRegistry",
            "A newly created operation is registered before it enters a replica payload.",
        ),
        edge(
            "Sequential",
            "Reduction",
            "A delivery begins before the exact captured payload is folded into the target state.",
        ),
        edge(
            "Reduction",
            "ActuationPass",
            "The committed merge result precedes the effect on the named target replica.",
        ),
        edge(
            "ActuationPass",
            "Sequential",
            "The target-bound effect completes before the delivery step completes.",
        ),
        edge(
            "Sequential",
            "merge-and-delivery-verifier",
            "Completed edit and delivery evidence enters the premise and convergence verdict.",
        ),
    ];
    DacBaseRecord {
        id: "FEX-DOM-DIST-01".to_string(),
        name: "State-based replicated JSON object".to_string(),
        family: ArtifactFamily::DomainExample,
        evidence_role: EvidenceRole::ProblemFirstConstruction,
        territory: TerritoryRecord {
            authorities: vec![
                source(
                    "FEX-SRC-CRDT-PROBLEM",
                    AuthorityKind::ProblemContract,
                    "formal/examples/case-studies/state-based-json-crdt/README.md",
                    "formal-examples-manifest-v1",
                    "Replicated JSON-object subset, source contract, construction boundary, relies, controls, and exclusions.",
                ),
                source(
                    "FEX-SRC-SHAPIRO-CRDT-2011",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1007/978-3-642-24550-3_29",
                    "Stabilization, Safety, and Security of Distributed Systems, 2011",
                    "Strong eventual consistency and the monotonic semilattice route for state-based CRDT convergence.",
                ),
                source(
                    "FEX-SRC-SHAPIRO-CRDT-RR7506",
                    AuthorityKind::PrimaryPaper,
                    "https://inria.hal.science/inria-00555588",
                    "INRIA Research Report 7506, 2011",
                    "Add-only sets ordered by inclusion, union as least upper bound, and uniquely identified replicated events.",
                ),
                source(
                    "FEX-SRC-KLEPPMANN-BERESFORD-JSON-2017",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1109/TPDS.2017.2697382",
                    "IEEE Transactions on Parallel and Distributed Systems 28(10), 2017",
                    "JSON map editing, concurrent values, deletion, delayed delivery, and convergence source behavior.",
                ),
            ],
            included_behavior: s(&[
                "Issue uniquely identified scalar assignments and deletes at disconnected replicas.",
                "Merge grow-only operation payloads under duplicate and reordered state delivery.",
                "Retain causally maximal concurrent assignments and prevent observed values from resurrecting after deletion.",
                "Require complete issued-operation delivery before accepting equal replica states and views.",
            ]),
            omissions: s(&[
                "JSON arrays, collaborative text, counters, subtree moves, schema behavior, garbage collection, and state compaction.",
                "Network protocols, durable storage, membership change, crash recovery, Byzantine behavior, and production integration.",
                "Performance, bandwidth, memory use, and conformance with Automerge, Yjs, or the full Kleppmann-Beresford datatype.",
            ]),
        },
        native_problem: NativeProblemRecord {
            actors: s(&["replica", "local editor", "state-delivery transport", "convergence observer"]),
            state: s(&[
                "replica identity and local operation counter",
                "per-replica grow-only operation payload",
                "operation identity, causal context, path, and action",
                "captured state messages and delivery history",
                "materialized JSON conflict-set view",
            ]),
            transitions: s(&[
                "issue a local assignment or delete",
                "capture the source-visible operation set",
                "register the operation and add it to one local payload",
                "capture a replica state as a message",
                "deliver a stale, duplicate, or reordered state",
                "join target and delivered payloads",
                "materialize causally maximal values",
                "observe convergence after complete delivery",
            ]),
            commitments: s(&[
                "fresh operation identity publication",
                "local operation insertion",
                "target-replica merge effect",
                "delivery completion",
                "complete-state and equal-view verdict",
            ]),
            inputs: s(&[
                "finite stable replica set",
                "nonempty JSON map path",
                "scalar assignment or delete action",
                "finite edit, capture, and delivery script",
            ]),
            outputs: s(&[
                "issued-operation registry",
                "final replica payloads",
                "materialized per-replica views",
                "edit, capture, and delivery witnesses",
                "typed structural trace",
            ]),
            failures: s(&[
                "operation identity collision or conflicting content",
                "non-inflationary local update or merge",
                "merge differs from exact set union",
                "effect target differs from named replica",
                "causal overwrite, deletion, or conflict retention differs from the separate evaluator",
                "equal replicas omit an issued operation",
                "complete replicas materialize unequal views",
            ]),
            obligations: s(&[
                "identity uniqueness",
                "local monotonicity",
                "merge inflation and exact least upper bound",
                "idempotence, commutativity, and associativity",
                "target binding",
                "causal overwrite and concurrent-value retention",
                "complete delivery accounting",
                "strong convergence under the delivery rely",
            ]),
        },
        stripped_roles: vec![
            StrippedRole { role: "identity".to_string(), domain_binding: "replica and operation identity".to_string(), preserved_relation: "Distinct source events retain distinct governed identities.".to_string() },
            StrippedRole { role: "local-authority".to_string(), domain_binding: "one replica payload".to_string(), preserved_relation: "Each participant changes only its named local state.".to_string() },
            StrippedRole { role: "monotone-state".to_string(), domain_binding: "grow-only operation set".to_string(), preserved_relation: "Governed updates move upward under the registered partial order.".to_string() },
            StrippedRole { role: "combine".to_string(), domain_binding: "set union".to_string(), preserved_relation: "The committed result is the exact least upper bound of both inputs.".to_string() },
            StrippedRole { role: "effect-target".to_string(), domain_binding: "delivery target replica".to_string(), preserved_relation: "A merge changes exactly the named local state.".to_string() },
            StrippedRole { role: "causal-marker".to_string(), domain_binding: "source-visible operation identities".to_string(), preserved_relation: "A later event dominates only events visible at its source.".to_string() },
            StrippedRole { role: "conflict-set".to_string(), domain_binding: "causally maximal assignments".to_string(), preserved_relation: "Concurrent values remain visible without selecting one global authority.".to_string() },
            StrippedRole { role: "execution-order".to_string(), domain_binding: "one finite runner interleaving".to_string(), preserved_relation: "Every executable edit and delivery has one begin and completion; this order does not define causality.".to_string() },
            StrippedRole { role: "observation".to_string(), domain_binding: "complete-state and equal-view verdict".to_string(), preserved_relation: "Complete delivery is checked before agreement is accepted as convergence.".to_string() },
        ],
        construction: ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes,
            edges,
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: s(&[
                "ResourceRegistry.Store for every operation and captured state identity",
                "Reduction.Commit for every delivered payload",
                "ActuationPass.Commit on the named replica",
                "Sequential.Complete for every edit, capture, and delivery",
                "complete issued-state and equal-view verification",
            ]),
            permitted_host_material: s(&[
                "owned ordered maps and sets for finite domain state",
                "JSON path and scalar value representation",
                "domain join and causal-maximality functions",
                "finite scripts and deterministic observation ordering",
            ]),
            scope_delta: Vec::new(),
            candidate_assessment: None,
        },
        relies: s(&[
            "The replica set used by one run is finite and stable.",
            "Each operation executes atomically at one source replica and receives a unique replica-counter identity.",
            "Correct replicas eventually receive state containing every issued operation.",
            "Operation content is not corrupted in transport.",
            "Each finite local edit, merge, query, and verification call terminates.",
            "The cited state-based CRDT convergence result applies to the declared monotonic semilattice and delivery premises.",
        ]),
        oracle: Some(OracleRecord {
            id: "FEX-REF-CRDT-ISSUED-OPERATIONS".to_string(),
            method: "A structure-free evaluator derives causally maximal values directly from the issued-operation registry, while a separate exact-union function reconstructs the least upper bound without calling the construction merge helper.".to_string(),
            implementation_identity: "formal-example-domains::crdt_reference::evaluate_issued_operations".to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "published concurrent assignment, offline different-path, overwrite, deletion, and concurrent delete/assign witnesses",
                "64 generated concurrent-assignment pairs and 8 generated path/edit/delivery-order cases",
                "six three-replica delivery permutations with duplicate delivery",
                "8-state merge family with 8 idempotence, 64 commutativity, and 512 associativity checks",
            ]),
            equivalence_relation: "Exact equality of complete replica payloads with the independently reconstructed issued-operation state and exact equality of materialized views with the issued-operation evaluator.".to_string(),
            common_mode_risks: s(&[
                "Construction and reference share the same operation and JSON value types.",
                "Both paths rely on the same recorded causal dependencies supplied at operation issue.",
                "The source theorem connecting the checked premises to unbounded convergence is cited rather than re-proved.",
            ]),
        }),
        controls: vec![
            control("FEX-CTRL-CRDT-REUSE-ID", ControlClass::Construction, "ResourceRegistry", "Give two distinct edits the same replica-counter identity.", "Registration or content-identity verification rejects the collision.", &["local monotonicity", "complete delivery"]),
            control("FEX-CTRL-CRDT-BYPASS-REDUCTION", ControlClass::Construction, "Sequential -> Reduction", "Copy one payload without invoking the shared fold.", "Per-delivery recipe binding and merge inflation reject the run.", &["target identity", "delivery completion"]),
            control("FEX-CTRL-CRDT-LEFT-BIASED", ControlClass::Construction, "Reduction", "Return only the target-local payload.", "Upper-bound, exact-union, law, and convergence checks reject the merge.", &["operation identity", "target effect"]),
            control("FEX-CTRL-CRDT-DUPLICATE-FRESH", ControlClass::Construction, "ResourceRegistry", "Re-identify operations during duplicate delivery.", "Idempotence, identity, and complete issued-state checks reject the run.", &["delivery target", "finite execution"]),
            control("FEX-CTRL-CRDT-DROP-CONTEXT", ControlClass::Construction, "json-operation-and-query", "Issue a later assignment without its source-visible dependencies.", "The independent evaluator rejects the claimed causal overwrite result.", &["operation identity", "merge union"]),
            control("FEX-CTRL-CRDT-LOSE-CONFLICT", ControlClass::Construction, "json-operation-and-query", "Resolve concurrent assignments by a total order instead of retaining all maxima.", "The separate evaluator rejects the view even when replicas agree.", &["complete delivery", "replica state equality"]),
            control("FEX-CTRL-CRDT-DROP-DELETE", ControlClass::Construction, "json-operation-and-query", "Omit a delete operation before stale state is redelivered.", "The deletion witness and issued-operation evaluator reject resurrection.", &["merge exactness", "duplicate delivery"]),
            control("FEX-CTRL-CRDT-MISDIRECT", ControlClass::Construction, "Reduction -> ActuationPass", "Apply a merge result to a replica other than the named target.", "Target-bound actuation and per-delivery evidence reject the run.", &["exact union", "sequential completion"]),
            control("FEX-CTRL-CRDT-INCOMPLETE", ControlClass::Construction, "Sequential -> merge-and-delivery-verifier", "Remove one issued operation from every compared replica.", "Complete-delivery accounting rejects agreement on an incomplete state.", &["replica equality", "view equality"]),
            control("FEX-CTRL-CRDT-REPEATED-ORDER", ControlClass::Construction, "ActuationPass -> Sequential", "Misorder a later delivery after one correctly ordered delivery.", "Per-delivery recipe verification rejects the later instance.", &["earlier delivery order", "merge result"]),
        ],
        relation: None,
        boundary: ClaimBoundary {
            claim: "For the registered finite JSON-object subset and delivery schedules, the shared-structure construction preserves the state-based merge premises, agrees with separate issued-operation and exact-union references, and converges after complete delivery, while the mechanized premise-binding model passes its positive and isolated-control checks.".to_string(),
            claim_ceiling: "Bounded executable reconstruction plus bounded model checking of identity, monotonicity, exact join, target, delivery, and convergence premises; the general strong-eventual-convergence implication remains a registered reliance on the cited CRDT results.".to_string(),
            residuals: s(&[
                "Executable evidence is bounded to the named scripts, generated value/path cases, and one finite merge-law state family.",
                "The formal model checks a finite replica and operation set and does not provide a Rust-to-TLA refinement theorem.",
                "Eventual delivery, atomic local operations, transport integrity, full JSON behavior, production integration, and performance remain outside the claim.",
            ]),
            falsifiers: s(&[
                "A complete registered run differs from the issued-operation or exact-union reference.",
                "Any checked merge law fails on the registered state family.",
                "Replica agreement is accepted while an issued operation or correct replica is omitted.",
                "Any named construction control passes the complete verifier.",
                "The formal premise-binding model fails a declared invariant or a paired control misses its target.",
                "A source-required governed state or commit cannot be placed in a retained structure, domain function, runtime rely, or explicit residual.",
            ]),
        },
    }
}

fn rdp_record() -> DacBaseRecord {
    let nodes = vec![
        shared_node(
            "ResourceRegistry",
            "formal-example-structures::resource_registry::ResourceRegistry",
            "Register account identities and account-local accepted query identities.",
        ),
        shared_node(
            "Budget",
            "formal-example-structures::budget::Budget",
            "Carry every additive fixed-order total and enforce the hard reported-epsilon ceiling.",
        ),
        shared_node(
            "CompetitiveSelection",
            "formal-example-structures::selection::CompetitiveSelection",
            "Select the least converted bound from the complete fixed-order candidate set.",
        ),
        shared_node(
            "ActuationPass",
            "formal-example-structures::actuation::ActuationPass",
            "Bind atomic candidate-account replacement to the requested account identity.",
        ),
        shared_node(
            "Sequential",
            "formal-example-structures::sequential::Sequential",
            "Record the adaptive request prefix and terminal decision order.",
        ),
        node(
            "rdp-projection",
            ConstructionStratum::Domain,
            "formal-example-domains::rdp::project_candidates",
            "Convert every cumulative fixed-order coordinate at the registered delta and scale.",
        ),
        node(
            "prefix-verifier",
            ConstructionStratum::Domain,
            "formal-example-domains::rdp::verify_run",
            "Reconstruct accepted prefixes, candidate sets, decisions, account isolation, and rejection noninterference.",
        ),
    ];
    let edges = vec![
        edge(
            "ResourceRegistry",
            "Sequential",
            "Only a request naming one registered account may begin a governed accounting step.",
        ),
        edge(
            "Sequential",
            "rdp-projection",
            "The request begins before its complete candidate curve is projected.",
        ),
        edge(
            "rdp-projection",
            "CompetitiveSelection",
            "Every registered order candidate enters the deterministic minimum selection.",
        ),
        edge(
            "CompetitiveSelection",
            "Budget",
            "The selected reported bound and every coordinate charge enter their capacity ledgers.",
        ),
        edge(
            "Budget",
            "ResourceRegistry",
            "Accepted charges commit before the query identity is published in its account scope.",
        ),
        edge(
            "ResourceRegistry",
            "ActuationPass",
            "The fully recorded candidate account enters the target-bound replacement effect.",
        ),
        edge(
            "ActuationPass",
            "Sequential",
            "Accepted account replacement completes before the request step completes.",
        ),
        edge(
            "Sequential",
            "prefix-verifier",
            "Completed decisions and account state enter the independent prefix verdict.",
        ),
    ];
    DacBaseRecord {
        id: "FEX-DOM-PRIV-01".to_string(),
        name: "Fixed-grid Renyi differential privacy accountant".to_string(),
        family: ArtifactFamily::DomainExample,
        evidence_role: EvidenceRole::ProblemFirstConstruction,
        territory: TerritoryRecord {
            authorities: vec![
                source(
                    "FEX-SRC-RDP-PROBLEM",
                    AuthorityKind::ProblemContract,
                    "formal/examples/case-studies/fixed-grid-rdp-accountant/README.md",
                    "formal-examples-manifest-v1",
                    "Fixed-grid RDP account, certificate and mediation relies, construction boundary, controls, and exclusions.",
                ),
                source(
                    "FEX-SRC-MIRONOV-RDP-2017",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1109/CSF.2017.11",
                    "30th IEEE Computer Security Foundations Symposium, 2017",
                    "Fixed-order RDP composition and conversion to an epsilon-delta differential privacy bound.",
                ),
                source(
                    "FEX-SRC-DWORK-ROTH-DP-2014",
                    AuthorityKind::PrimaryTextbook,
                    "https://doi.org/10.1561/0400000042",
                    "Foundations and Trends in Theoretical Computer Science 9(3-4), 2014",
                    "Differential privacy definition and sound additive basic composition used to correct the original scalar-control premise.",
                ),
            ],
            included_behavior: s(&[
                "Compose certified query costs additively at six registered Renyi orders.",
                "Convert every cumulative coordinate to an epsilon candidate at delta exp(-24) and select the least candidate.",
                "Admit a release only when the selected bound remains within an account-specific hard ceiling.",
                "Preserve account isolation, query identity, accepted-prefix order, and rejection noninterference.",
            ]),
            omissions: s(&[
                "Mechanism sampling, sensitivity analysis, noise calibration, certificate generation, and access to private datasets.",
                "Subsampling amplification, privacy-loss distributions, continuous-order optimization, floating-point accounting, and group privacy.",
                "Production mediation, crash recovery, distributed transactions, utility, performance, and comparison with specialized accountants.",
            ]),
        },
        native_problem: NativeProblemRecord {
            actors: s(&["privacy account", "certified query caller", "accountant", "release boundary", "audit observer"]),
            state: s(&[
                "account identity, adjacency relation, target delta, and epsilon ceiling",
                "one cumulative cost ledger per registered order",
                "account-local accepted query registry",
                "reported epsilon, winning order, and reported-bound capacity ledger",
                "accepted and rejected request history",
            ]),
            transitions: s(&[
                "validate account, identity, and complete certified curve",
                "extend every fixed-order coordinate",
                "convert every coordinate at the fixed delta",
                "select the minimum converted bound",
                "accept within the hard ceiling or reject without mutation",
                "register the accepted query and replace the named account",
                "authorize one release",
                "verify the complete accepted prefix",
            ]),
            commitments: s(&[
                "per-order Budget charges",
                "reported-bound Budget charge or rejection",
                "account-local query identity publication",
                "target-bound account replacement and release count",
                "ordered request completion",
            ]),
            inputs: s(&[
                "registered account identity",
                "unique query identity within that account",
                "one nonnegative certified cost per fixed order",
                "finite adaptive request sequence",
            ]),
            outputs: s(&[
                "accept or reject decision",
                "cumulative fixed-order curve",
                "reported epsilon and winning order",
                "accepted query count and release count",
                "typed structural trace",
            ]),
            failures: s(&[
                "unknown account, duplicate identity, malformed curve, or arithmetic overflow",
                "coordinate ledger differs from declared accepted costs",
                "conversion or complete candidate set differs from the registered projection",
                "selected bound exceeds the hard ceiling",
                "rejected request mutates state or authorizes release",
                "accepted request changes another account or omits a governed commit",
            ]),
            obligations: s(&[
                "account and query identity",
                "complete fixed-order declaration",
                "exact additive coordinate composition",
                "registered conversion and complete minimum selection",
                "hard reported-epsilon capacity",
                "target-bound accepted commit",
                "rejection noninterference",
                "adaptive sequential prefix order",
                "certificate and mediation relies",
            ]),
        },
        stripped_roles: vec![
            StrippedRole { role: "governed-identity".to_string(), domain_binding: "account and query identities".to_string(), preserved_relation: "One accepted effect maps to one declared authority and certificate.".to_string() },
            StrippedRole { role: "parallel-ledgers".to_string(), domain_binding: "one cumulative value per registered order".to_string(), preserved_relation: "Every accepted item contributes its declared amount to every coordinate.".to_string() },
            StrippedRole { role: "projection".to_string(), domain_binding: "RDP-to-DP conversion at one order".to_string(), preserved_relation: "Each governed coordinate maps to one claim candidate at the fixed delta.".to_string() },
            StrippedRole { role: "quality-order".to_string(), domain_binding: "converted epsilon and alpha tie key".to_string(), preserved_relation: "The least registered bound is selected deterministically.".to_string() },
            StrippedRole { role: "hard-capacity".to_string(), domain_binding: "reported epsilon ceiling".to_string(), preserved_relation: "A selected candidate cannot commit above the configured limit.".to_string() },
            StrippedRole { role: "effect-target".to_string(), domain_binding: "named privacy account".to_string(), preserved_relation: "All accepted accounting state changes one selected resource.".to_string() },
            StrippedRole { role: "execution-order".to_string(), domain_binding: "adaptive accepted request prefix".to_string(), preserved_relation: "A later certificate may depend on earlier released results and extends the prefix once.".to_string() },
            StrippedRole { role: "evidence-relation".to_string(), domain_binding: "certificate, coordinate charges, selected bound, and release".to_string(), preserved_relation: "Every accepted effect has one cross-checked accounting account.".to_string() },
        ],
        construction: ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes,
            edges,
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: s(&[
                "Budget.Commit on every fixed-order coordinate for an accepted query",
                "CompetitiveSelection.Commit on the complete converted candidate set",
                "Budget.Commit or Budget.Reject at the reported-epsilon ceiling",
                "ResourceRegistry.Store for an accepted query identity",
                "ActuationPass.Commit on the requested account",
                "Sequential.Complete for every accepted or rejected request",
            ]),
            permitted_host_material: s(&[
                "checked integer arithmetic at the declared micro-epsilon scale",
                "owned finite vectors for the fixed order grid and query declarations",
                "stateless RDP-to-DP projection over governed ledger values",
                "atomic replacement of one completed candidate account as a runtime rely",
            ]),
            scope_delta: Vec::new(),
            candidate_assessment: None,
        },
        relies: s(&[
            "Every accepted query certificate is a valid RDP upper bound at every registered order under the account's immutable adjacency relation.",
            "All privacy-relevant releases at the selected boundary are mediated by this accountant.",
            "An accepted certified mechanism executes and releases at most once under its query identity; a rejected request releases nothing.",
            "Submitted integer costs conservatively represent the certified values without round-down.",
            "The runtime atomically replaces one fully constructed account state at the recorded commit.",
            "The cited RDP composition and conversion results apply to the declared fixed-order adaptive composition.",
        ]),
        oracle: Some(OracleRecord {
            id: "FEX-REF-RDP-PREFIX".to_string(),
            method: "A structure-free evaluator reads only the configuration and accepted query declarations, independently sums every coordinate, converts every registered order, selects the deterministic minimum, and reconstructs each accepted prefix.".to_string(),
            implementation_identity: "formal-example-domains::rdp_reference::evaluate_prefix".to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "seven-request two-account demonstration with six accepts and one hard-ceiling rejection",
                "winning-order sequence 17, 17, 17, 9 and final epsilon 4.8 at order 9 for scope-a",
                "90 generated workload configurations and 315 separately recomputed request decisions",
                "account-local identity, malformed-curve, and rejection noninterference witnesses",
            ]),
            equivalence_relation: "Exact equality of every accepted-prefix cumulative curve, converted candidate set, selected epsilon and order, accept or reject decision, final account state, and release count.".to_string(),
            common_mode_risks: s(&[
                "Construction and evaluator separately transcribe the same published closed-form conversion.",
                "Both paths consume the same declared query certificates and fixed order configuration.",
                "A shared source-formula transcription error is outside differential testing and leaves the primary paper load-bearing.",
            ]),
        }),
        controls: vec![
            control("FEX-CTRL-RDP-REUSE-ID", ControlClass::Construction, "ResourceRegistry", "Reuse an accepted query identity within one account.", "The account-local registry rejects replacement.", &["account target", "prior ledger state"]),
            control("FEX-CTRL-RDP-OMIT-ORDER", ControlClass::Construction, "Budget", "Skip one fixed-order coordinate charge for an accepted query.", "Independent curve and cross-ledger checks reject the account.", &["other coordinate charges", "query identity"]),
            control("FEX-CTRL-RDP-DOUBLE-ORDER", ControlClass::Construction, "Budget", "Charge one fixed-order coordinate twice.", "Independent curve and reported-bound checks reject the account.", &["reported capacity", "query identity"]),
            control("FEX-CTRL-RDP-DROP-DELTA", ControlClass::Construction, "rdp-projection", "Drop the conversion penalty and treat cumulative RDP epsilon as the reported candidate.", "Projection verification rejects the run even while every capacity ledger remains green.", &["coordinate capacity", "query identity", "release count"]),
            control("FEX-CTRL-RDP-OMIT-BEST", ControlClass::Construction, "rdp-projection -> CompetitiveSelection", "Remove the true minimum order candidate before selection.", "Complete-candidate reconstruction and winner checks reject the selection.", &["remaining candidate order", "reported capacity"]),
            control("FEX-CTRL-RDP-SUM-STANDALONE", ControlClass::Construction, "rdp-projection", "Sum per-query converted bounds instead of composing the RDP curve before conversion.", "The prefix evaluator rejects the conservative but claim-inexact account.", &["hard capacity", "release identity"]),
            control("FEX-CTRL-RDP-BYPASS-CEILING", ControlClass::Construction, "CompetitiveSelection -> Budget", "Commit a query whose selected reported bound exceeds the hard ceiling.", "Capacity, decision, and cross-ledger identities reject the release.", &["complete candidate set", "account target"]),
            control("FEX-CTRL-RDP-MISDIRECT", ControlClass::Construction, "ResourceRegistry -> ActuationPass", "Apply an accepted candidate state to another account.", "Target binding and account isolation reject the run.", &["query registration", "reported capacity"]),
            control("FEX-CTRL-RDP-MUTATE-REJECT", ControlClass::Construction, "Budget -> Sequential", "Charge account state after the reported Budget rejects the request.", "Full before-after equality rejects the mutated rejection.", &["rejection decision", "release count"]),
            control("FEX-CTRL-RDP-REPEATED-ORDER", ControlClass::Construction, "ActuationPass -> Sequential", "Place a later accepted account effect before its selection evidence.", "Per-request recipe verification rejects the later instance.", &["earlier request order", "final prefix state"]),
        ],
        relation: None,
        boundary: ClaimBoundary {
            claim: "For the registered fixed order grid, integer scale, target delta, certified query declarations, and bounded workloads, the shared-structure construction composes every coordinate, selects and enforces the registered reported bound, and agrees with a separate prefix evaluator, while the mechanized premise-binding model passes its positive and isolated-control checks.".to_string(),
            claim_ceiling: "Bounded executable reconstruction plus bounded model checking of declaration, projection, selection, capacity, target, and noninterference premises; the conditional privacy implication and conversion formula remain registered relies on the cited source theorem and valid query certificates.".to_string(),
            residuals: s(&[
                "The executable workload evidence is bounded to the registered demonstration and generated grid.",
                "Construction and reference can share a transcription error in the closed-form conversion; the primary RDP paper remains the formula authority.",
                "Certificate truth, total release mediation, runtime atomic replacement, continuous-order optimality, production behavior, and performance remain outside the claim.",
            ]),
            falsifiers: s(&[
                "Any accepted coordinate, converted candidate, selected bound, decision, or final account differs from the separate prefix evaluator.",
                "A request commits above its hard ceiling, changes another account, or mutates state after rejection.",
                "A named construction control passes the complete verifier.",
                "The formal positive model fails a declared invariant or a paired control misses its target.",
                "The registered conversion differs from the cited theorem after source review.",
                "A source-required governed state or commit cannot be placed without inventing unclassified behavior.",
            ]),
        },
    }
}

fn stm_record() -> DacBaseRecord {
    let nodes = vec![
        shared_node(
            "ResourceRegistry",
            "formal-example-structures::resource_registry::ResourceRegistry",
            "Register shared cells and begun transaction identities without replacement.",
        ),
        shared_node(
            "RelationshipGraph",
            "formal-example-structures::relationship_graph::RelationshipGraph",
            "Commit each transaction's declared read and write relation to shared cells.",
        ),
        shared_node(
            "ActuationPass",
            "formal-example-structures::actuation::ActuationPass",
            "Carry every buffered write target into one complete target-bound effect batch.",
        ),
        shared_node(
            "Sequential",
            "formal-example-structures::sequential::Sequential",
            "Record one finite interleaving of transaction microsteps without supplying a serial transaction order.",
        ),
        node(
            "global-epoch-protocol",
            ConstructionStratum::Domain,
            "formal-example-domains::stm::run_script",
            "Validate stable reads, buffer writes, acquire one odd publication interval, and publish after the complete batch.",
        ),
        node(
            "atomic-epoch-word",
            ConstructionStratum::Runtime,
            "std::sync::atomic::AtomicU64",
            "Supply the single-word sequentially consistent compare-exchange and epoch load/store rely.",
        ),
        node(
            "opacity-verifier",
            ConstructionStratum::Domain,
            "formal-example-domains::stm::verify_run",
            "Bind identity, access, epoch, target, publication, abort, and finite opacity observations.",
        ),
    ];
    let edges = vec![
        edge(
            "ResourceRegistry",
            "RelationshipGraph",
            "Declared transaction access edges resolve only to registered cell and transaction identities.",
        ),
        edge(
            "RelationshipGraph",
            "Sequential",
            "The complete access declaration commits before transaction microsteps begin.",
        ),
        edge(
            "Sequential",
            "global-epoch-protocol",
            "Each selected microstep begins before its read, buffer, validation, acquisition, or publication action.",
        ),
        edge(
            "global-epoch-protocol",
            "atomic-epoch-word",
            "Stable reads and writing commits use the recorded start epoch at the runtime atomic boundary.",
        ),
        edge(
            "atomic-epoch-word",
            "ActuationPass",
            "A successful even-to-odd acquisition precedes every shared write effect.",
        ),
        edge(
            "ActuationPass",
            "atomic-epoch-word",
            "Every buffered target effect precedes odd-to-even publication.",
        ),
        edge(
            "atomic-epoch-word",
            "Sequential",
            "Commit publication or abort completes before the corresponding microstep completes.",
        ),
        edge(
            "Sequential",
            "opacity-verifier",
            "The terminal finite history enters real-time-respecting serial replay.",
        ),
    ];
    DacBaseRecord {
        id: "FEX-DOM-TXN-01".to_string(),
        name: "Bounded optimistic software transactional memory".to_string(),
        family: ArtifactFamily::DomainExample,
        evidence_role: EvidenceRole::ProblemFirstConstruction,
        territory: TerritoryRecord {
            authorities: vec![
                source(
                    "FEX-SRC-STM-PROBLEM",
                    AuthorityKind::ProblemContract,
                    "formal/examples/case-studies/optimistic-stm/README.md",
                    "formal-examples-manifest-v1",
                    "Finite word-heap STM contract, runtime atomicity boundary, construction, controls, and exclusions.",
                ),
                source(
                    "FEX-SRC-HERLIHY-MOSS-TM-1993",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1145/165123.165164",
                    "20th International Symposium on Computer Architecture, 1993",
                    "Transaction abstraction and atomic multi-word read-modify-write source behavior.",
                ),
                source(
                    "FEX-SRC-SHAVIT-TOUITOU-STM-1995",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1145/224964.224987",
                    "14th ACM Symposium on Principles of Distributed Computing, 1995",
                    "Software transactional memory above single-word atomic synchronization.",
                ),
                source(
                    "FEX-SRC-TL2-2006",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1007/11864219_14",
                    "20th International Symposium on Distributed Computing, 2006",
                    "Commit-time locking, global version-clock validation, and consistent-memory execution route.",
                ),
                source(
                    "FEX-SRC-OPACITY-2008",
                    AuthorityKind::PrimaryPaper,
                    "https://doi.org/10.1145/1345206.1345233",
                    "13th ACM SIGPLAN Symposium on Principles and Practice of Parallel Programming, 2008",
                    "Opacity as a real-time-respecting serial explanation for committed and non-committed transaction observations.",
                ),
                source(
                    "FEX-SRC-THEORY-DAC-ATOMICITY",
                    AuthorityKind::ProjectDecomposition,
                    "docs/domain-abstraction-collapse.md atomicity and transaction-manager passages",
                    "repository publication edition",
                    "Project boundary placing transaction management as a provider of runtime atomicity rather than a new Transaction primitive.",
                ),
            ],
            included_behavior: s(&[
                "Run nonnested transactions over a finite signed-integer word heap with declared read/write access relations.",
                "Return only transaction-local writes or shared values surrounded by the same even start epoch.",
                "Abort stale writers and publish a complete multi-cell write batch through one odd epoch interval.",
                "Check committed and aborted observations against exhaustive real-time-respecting serial replay.",
            ]),
            omissions: s(&[
                "Nested transactions, irrevocable effects, allocation and reclamation, nontransactional heap access, and counter exhaustion.",
                "Writer crash recovery, persistence, distributed transactions, weak-memory proof, and automatic retry or progress guarantees.",
                "Production integration, throughput, latency, scalability, and comparison with specialized STM implementations.",
            ]),
        },
        native_problem: NativeProblemRecord {
            actors: s(&["transaction declaration", "transaction-local context", "finite shared heap", "global epoch owner", "interleaving scheduler", "opacity observer"]),
            state: s(&[
                "cell identity and value",
                "transaction identity, access relation, start epoch, and status",
                "ordered reads and buffered writes",
                "global even or odd epoch",
                "write-batch target and applied-effect records",
                "finite begin and end positions",
            ]),
            transitions: s(&[
                "register cells and declared accesses",
                "begin at an even epoch or abort at an odd epoch",
                "validate-read-revalidate one shared cell",
                "buffer one local write",
                "compare-exchange the start epoch from even to odd",
                "apply every buffered write target",
                "publish the next even epoch or abort without effects",
                "search for an opaque serialization",
            ]),
            commitments: s(&[
                "cell and transaction identity registration",
                "declared access graph commit",
                "odd epoch acquisition",
                "target-bound buffered write effects",
                "even epoch publication after all effects",
                "transaction terminal status and step completion",
            ]),
            inputs: s(&[
                "finite unique cell declarations",
                "finite unique transaction declarations and access modes",
                "finite local-order-preserving microstep schedule",
                "single-word atomic epoch runtime",
            ]),
            outputs: s(&[
                "final heap and epoch",
                "committed and aborted transaction records",
                "read observations and applied writes",
                "opaque serialization witness",
                "typed structural trace",
            ]),
            failures: s(&[
                "duplicate identity or undeclared access",
                "read exposed from a changed or odd epoch",
                "stale writer commit or invalid epoch transition",
                "omitted or misdirected buffered write",
                "even publication before the complete effect batch",
                "aborted transaction changes shared state",
                "history has no opaque serialization",
            ]),
            obligations: s(&[
                "identity and declared access scope",
                "stable read snapshot and read-own-write",
                "write conflict detection and exclusive publication",
                "complete target-bound write batch",
                "publication after every effect",
                "abort noninterference",
                "real-time-respecting atomic appearance",
                "ordered finite execution",
                "single-word atomic runtime rely",
            ]),
        },
        stripped_roles: vec![
            StrippedRole { role: "governed-identity".to_string(), domain_binding: "cell and transaction identities".to_string(), preserved_relation: "State and effects remain attributable to one declared resource.".to_string() },
            StrippedRole { role: "declared-relation".to_string(), domain_binding: "transaction-to-cell read/write edge".to_string(), preserved_relation: "An operation may touch only its registered target and mode.".to_string() },
            StrippedRole { role: "snapshot-marker".to_string(), domain_binding: "even transaction start epoch".to_string(), preserved_relation: "Every exposed shared read belongs to one unchanged committed state.".to_string() },
            StrippedRole { role: "local-buffer".to_string(), domain_binding: "ordered reads and pending writes".to_string(), preserved_relation: "Speculative effects remain private until acceptance.".to_string() },
            StrippedRole { role: "exclusion-marker".to_string(), domain_binding: "odd global epoch".to_string(), preserved_relation: "At most one writer owns the publication interval.".to_string() },
            StrippedRole { role: "validation".to_string(), domain_binding: "start and current epoch equality".to_string(), preserved_relation: "Stale speculative work aborts before publication.".to_string() },
            StrippedRole { role: "effect-batch".to_string(), domain_binding: "buffered write targets".to_string(), preserved_relation: "Every accepted effect reaches exactly the declared cell set.".to_string() },
            StrippedRole { role: "publication".to_string(), domain_binding: "next even epoch".to_string(), preserved_relation: "The complete batch becomes observable only after all effects.".to_string() },
            StrippedRole { role: "execution-order".to_string(), domain_binding: "finite interleaving of microsteps".to_string(), preserved_relation: "Concurrent histories are represented without assuming one transaction order.".to_string() },
            StrippedRole { role: "observation".to_string(), domain_binding: "real-time-respecting serial replay".to_string(), preserved_relation: "Committed and aborted reads have one legal state explanation.".to_string() },
        ],
        construction: ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes,
            edges,
            execution_carrier: "Sequential microstep interleaving".to_string(),
            governed_commit_points: s(&[
                "ResourceRegistry.Store for each begun transaction",
                "RelationshipGraph.Commit for the declared access scope",
                "AtomicU64 compare_exchange from the recorded even epoch to odd",
                "ActuationPass.Commit for every buffered write target",
                "AtomicU64 store of the next even epoch after every effect",
                "Sequential.Complete for every microstep",
                "finite opacity verdict and serialization witness",
            ]),
            permitted_host_material: s(&[
                "owned finite maps and vectors for heap cells, read observations, and buffered writes",
                "transaction status and epoch values as Marker and Counter connective forms",
                "checked finite schedule interpretation",
                "standard-library AtomicU64 at the declared runtime boundary",
            ]),
            scope_delta: Vec::new(),
            candidate_assessment: None,
        },
        relies: s(&[
            "Every shared heap access at the selected boundary is mediated by this transaction manager.",
            "Sequentially consistent AtomicU64 load, store, and compare-exchange provide their documented single-word atomic behavior.",
            "A writer that acquires the odd epoch runs to publication; crash recovery while odd is excluded.",
            "Transaction code performs no irrevocable external effect before commit.",
            "The finite epoch values used by the registered cases do not overflow.",
            "The value-level exhaustive serialization criterion is an adequate executable projection of opacity for the registered word-heap histories.",
        ]),
        oracle: Some(OracleRecord {
            id: "FEX-REF-STM-OPACITY".to_string(),
            method: "A structure-free evaluator enumerates every transaction order that respects observed real-time precedence, replays ordered reads and local writes for committed and aborted transactions, applies only committed writes, and requires exact final-heap equality.".to_string(),
            implementation_identity: "formal-example-domains::stm_reference::evaluate_opacity".to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "two-cell atomic-publication and torn-read schedules",
                "two conflicting writers begun at one epoch",
                "all 924 local-order-preserving interleavings of two six-step transaction programs",
                "eight premise and outcome controls",
            ]),
            equivalence_relation: "Existence of one real-time-respecting serial order in which every recorded read returns the replayed value, aborted writes have no effect, committed writes produce the exact observed final heap, and every transaction appears once.".to_string(),
            common_mode_risks: s(&[
                "Construction and reference share transaction operation records and the finite signed-integer cell model.",
                "The value-level oracle is a bounded projection of the published general opacity definition.",
                "Runtime atomic and memory-order semantics are assumed rather than independently simulated by the oracle.",
            ]),
        }),
        controls: vec![
            control("FEX-CTRL-STM-REUSE-ID", ControlClass::Construction, "ResourceRegistry", "Begin a second transaction under an existing identity.", "The transaction registry rejects replacement.", &["cell registry", "access graph"]),
            control("FEX-CTRL-STM-UNDECLARED", ControlClass::Construction, "RelationshipGraph", "Read a cell absent from the transaction's declared access relation.", "Graph-to-operation verification rejects the history.", &["cell identity", "sequential order"]),
            control("FEX-CTRL-STM-IGNORE-EPOCH", ControlClass::Construction, "global-epoch-protocol", "Expose reads while the epoch is odd or differs from the transaction start.", "The torn read has no opaque serialization.", &["read-own-write", "final heap"]),
            control("FEX-CTRL-STM-STALE-WRITER", ControlClass::Construction, "global-epoch-protocol -> atomic-epoch-word", "Acquire from the current epoch instead of the transaction's recorded start epoch.", "Epoch identity and opacity reject two stale committed writers.", &["complete write batch", "final heap"]),
            control("FEX-CTRL-STM-OMIT-TARGET", ControlClass::Construction, "ActuationPass", "Remove one buffered cell from the write effect batch.", "Exact write-set and final-state checks reject the commit.", &["epoch acquisition", "remaining target effect"]),
            control("FEX-CTRL-STM-MISDIRECT", ControlClass::Construction, "ActuationPass", "Allocate one write effect to another shared cell.", "Effect-target identity and opacity reject the commit.", &["write coverage", "epoch publication"]),
            control("FEX-CTRL-STM-EARLY-PUBLISH", ControlClass::Construction, "ActuationPass -> atomic-epoch-word", "Publish an even epoch after only one effect in a two-cell batch.", "Publication sequencing and a torn reader reject the history.", &["epoch acquisition", "first target effect"]),
            control("FEX-CTRL-STM-PARTIAL-ABORT", ControlClass::Construction, "global-epoch-protocol", "Record abort after applying the first buffered write.", "Abort noninterference and final-state replay reject the history.", &["target identity", "terminal even epoch"]),
        ],
        relation: None,
        boundary: ClaimBoundary {
            claim: "For the registered finite word heaps, nonnested transaction declarations, and bounded schedules, the shared-structure construction provides stable-epoch reads, conflict abort, and complete target-bound write publication, and it produces histories accepted by a separate opacity evaluator; the mechanized premise-binding model passes its positive and isolated-control checks.".to_string(),
            claim_ceiling: "Bounded executable reconstruction plus exhaustive finite interleavings and bounded model checking above one explicit single-word atomic runtime rely; the published transactional-memory and opacity definitions remain source authorities for the general abstraction.".to_string(),
            residuals: s(&[
                "The exhaustive Rust evidence is bounded to the registered word heaps, transaction programs, and finite schedules.",
                "The formal model and value-level oracle are finite abstractions and do not provide a Rust-to-TLA refinement theorem or general opacity proof.",
                "Weak memory, crashes, nesting, nontransactional access, progress, persistence, production behavior, and performance remain outside the claim.",
            ]),
            falsifiers: s(&[
                "Any registered honest history lacks a real-time-respecting opaque serialization.",
                "A committed writer omits or misdirects a buffered write or publishes before every effect.",
                "An aborted transaction changes the shared heap.",
                "Any named construction control passes the complete verifier.",
                "The formal positive model fails a declared invariant or a paired control misses its target.",
                "A source-required governed state or commit remains after the retained structures, connective forms, and single-word runtime rely are placed.",
            ]),
        },
    }
}

fn cicd_record(id: &str) -> DacBaseRecord {
    let oracle = match id {
        "FEX-DOM-CICD-01" => OracleRecord {
            id: "FEX-REF-CICD-DEPENDENCY-ENUMERATOR".to_string(),
            method: "Depth-first enumeration over a separate plain-state job, worker, barrier, and publication transition relation.".to_string(),
            implementation_identity: "formal-example-domains::cicd_reference::enumerate_dependency_schedules".to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "four job identities and four dependency edges",
                "two test worker identities",
                "start-before-complete lifecycle order",
                "barrier-before-publication order",
                "six named final outputs",
                "closed-form schedule cardinality 6 * C(10, 2) = 270",
            ]),
            equivalence_relation: "The complete accepted event-schedule set is equal in both directions, and every accepted construction schedule produces the exact registered output set.".to_string(),
            common_mode_risks: s(&[
                "Both paths interpret the same frozen source contract, so a shared source misunderstanding remains possible.",
                "The oracle does not import the catalog crate or call construction helpers; the carrier schedule set is enumerated through the actual StepGraph and ForkJoin transitions.",
            ]),
        },
        "FEX-DOM-CICD-03" => OracleRecord {
            id: "FEX-REF-CICD-PARTITION-ENUMERATOR".to_string(),
            method: "Depth-first enumeration over a separate plain-state job, worker, barrier, and publication transition relation.".to_string(),
            implementation_identity: "formal-example-domains::cicd_reference::enumerate_partition_schedules".to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "four job identities and four dependency edges",
                "two test worker identities",
                "start-before-complete lifecycle order",
                "barrier-before-publication order",
                "six named final outputs",
                "closed-form schedule cardinality 6 * C(10, 2) = 270",
            ]),
            equivalence_relation: "The complete accepted event-schedule set is equal in both directions, and every accepted construction schedule produces the exact registered output set.".to_string(),
            common_mode_risks: s(&[
                "Both paths interpret the same frozen source contract, so a shared source misunderstanding remains possible.",
                "The oracle does not import the catalog crate or call construction helpers; the carrier schedule set is enumerated through the actual StepGraph and ForkJoin transitions.",
            ]),
        },
        "FEX-ASM-06" => OracleRecord {
            id: "FEX-REF-CICD-SCHEDULE-ENUMERATOR".to_string(),
            method: "Depth-first enumeration over a separate plain-state job, worker, barrier, and publication transition relation.".to_string(),
            implementation_identity: "formal-example-domains::cicd_reference::enumerate_schedules".to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: s(&[
                "four job identities and four dependency edges",
                "two test worker identities",
                "start-before-complete lifecycle order",
                "barrier-before-publication order",
                "six named final outputs",
                "closed-form schedule cardinality 6 * C(10, 2) = 270",
            ]),
            equivalence_relation: "The complete accepted event-schedule set is equal in both directions, and every accepted construction schedule produces the exact registered output set.".to_string(),
            common_mode_risks: s(&[
                "Both paths interpret the same frozen source contract, so a shared source misunderstanding remains possible.",
                "The oracle does not import the catalog crate or call construction helpers; the carrier schedule set is enumerated through the actual StepGraph and ForkJoin transitions.",
            ]),
        },
        _ => panic!("unregistered CI/CD evidence identity"),
    };
    let (name, family, evidence_role, claim, claim_ceiling) = match id {
        "FEX-DOM-CICD-01" => (
            "Pipeline DAG",
            ArtifactFamily::DomainExample,
            EvidenceRole::DomainReconstruction,
            "A bounded CI job-dependency DAG uses RelationshipGraph, TraversalEngine, and StepGraph, and its accepted schedules agree with an independent dependency enumerator.",
            "Exact accepted-schedule equality for the registered immutable four-job dependency graph.",
        ),
        "FEX-DOM-CICD-03" => (
            "Parallel test execution",
            ArtifactFamily::DomainExample,
            EvidenceRole::DomainReconstruction,
            "A bounded complete test matrix uses ResourceRegistry, Budget<Compute>, and ForkJoin; every declared partition appears in the joined output and accepted schedules agree with an independent enumerator.",
            "Exact partition completion and accepted-schedule equality for the registered two-worker matrix.",
        ),
        "FEX-ASM-06" => (
            "CI/CD pipeline",
            ArtifactFamily::IntegratedReconstruction,
            EvidenceRole::SourceReconstruction,
            "The bounded CI pipeline invokes one outer StepGraph and a nested ForkJoin test stage, crosses the registered identity, dependency, capacity, target-effect, and carrier-handoff seams, and agrees with an independent schedule oracle.",
            "Bounded executable reconstruction of the registered successful workflow and its nested carrier handoff.",
        ),
        _ => panic!("unregistered CI/CD evidence identity"),
    };
    DacBaseRecord {
        id: id.to_string(),
        name: name.to_string(),
        family,
        evidence_role,
        territory: TerritoryRecord {
            authorities: vec![
                source(
                    "FEX-SRC-CICD-PROBLEM",
                    AuthorityKind::ProblemContract,
                    "formal/examples/case-studies/nested-ci-cd-pipeline/README.md",
                    "formal-examples-manifest-v1",
                    "Frozen successful-workflow contract, DAC record, controls, evidence boundaries, and exclusions.",
                ),
                source(
                    "FEX-SRC-GITHUB-ACTIONS-JOBS",
                    AuthorityKind::ExecutableAuthority,
                    "https://docs.github.com/en/actions/how-tos/write-workflows/choose-what-workflows-do/use-jobs",
                    "GitHub Actions documentation, retrieved 2026-08-26",
                    "Operational source for job identities, dependency release, parallel jobs, and matrix expansion.",
                ),
                source(
                    "FEX-SRC-GITHUB-ACTIONS-WORKFLOW-SYNTAX",
                    AuthorityKind::ExecutableAuthority,
                    "https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax",
                    "GitHub Actions documentation, retrieved 2026-08-26",
                    "Operational source for jobs.<job_id>.needs, default parallelism, and matrix job behavior.",
                ),
            ],
            included_behavior: s(&[
                "Register four immutable job identities and two required test partitions.",
                "Release a job only after every declared predecessor completes.",
                "Permit the static-analysis and test branches to progress in either order after compilation.",
                "Complete both test workers before crossing one barrier and publishing the joined test output.",
                "Charge each declared unit of work and apply its effect to the named output resource.",
            ]),
            omissions: s(&[
                "Conditional jobs, failures, retries, cancellation, timeouts, runner provisioning, caching, secrets, and deployment behavior.",
                "GitHub Actions product conformance, arbitrary graph support, throughput, wall-clock duration, and performance comparison.",
            ]),
        },
        native_problem: NativeProblemRecord {
            actors: s(&[
                "workflow declaration",
                "dependency-controlled job",
                "test partition worker",
                "join barrier",
                "output observer",
            ]),
            state: s(&[
                "registered job and partition identities",
                "declared dependency edges",
                "per-job lifecycle state",
                "per-worker lifecycle state",
                "join phase and output status",
                "compute debit account",
                "materialized outputs",
            ]),
            transitions: s(&[
                "release a dependency-ready job",
                "start and complete a job",
                "start and complete a test worker",
                "cross the barrier after complete worker coverage",
                "publish the joined test output",
                "charge work and apply a named effect",
            ]),
            commitments: s(&[
                "exact identity publication",
                "declared dependency release",
                "complete test-partition coverage",
                "barrier-before-output order",
                "declared debit and target-effect identity",
            ]),
            inputs: s(&[
                "four fixed job identities",
                "four directed dependency edges",
                "two fixed test partition identities",
                "six compute units",
            ]),
            outputs: s(&[
                "six named outputs",
                "completed outer and inner carrier state",
                "accepted schedule set",
                "typed structural trace",
            ]),
            failures: s(&[
                "execution before dependency completion",
                "carrier edge differs from the declaration",
                "worker completion is omitted",
                "joined output is published before the barrier",
                "declared work is not charged",
                "effect target differs from the named output",
                "required carrier is bypassed",
            ]),
            obligations: s(&[
                "exact identity",
                "complete dependency relation",
                "dependency-governed release",
                "complete partition coverage",
                "barrier order",
                "debit identity",
                "target-effect identity",
                "outer-to-inner carrier handoff",
            ]),
        },
        stripped_roles: vec![
            StrippedRole {
                role: "identity".to_string(),
                domain_binding: "job and test-partition identifiers".to_string(),
                preserved_relation: "Only registered identities can own governed work or output.".to_string(),
            },
            StrippedRole {
                role: "dependency".to_string(),
                domain_binding: "jobs.<job_id>.needs edges".to_string(),
                preserved_relation: "An item becomes eligible only after every incoming predecessor completes.".to_string(),
            },
            StrippedRole {
                role: "frontier".to_string(),
                domain_binding: "reachable workflow jobs".to_string(),
                preserved_relation: "Every declared job is reached once from the workflow root.".to_string(),
            },
            StrippedRole {
                role: "worker-set".to_string(),
                domain_binding: "the two required test matrix partitions".to_string(),
                preserved_relation: "The joined result covers every declared sibling.".to_string(),
            },
            StrippedRole {
                role: "barrier".to_string(),
                domain_binding: "test-matrix aggregation point".to_string(),
                preserved_relation: "Output publication follows completion of the full worker set.".to_string(),
            },
            StrippedRole {
                role: "capacity".to_string(),
                domain_binding: "six declared compute units".to_string(),
                preserved_relation: "Committed work cannot exceed capacity and exact debit identity is checked separately.".to_string(),
            },
            StrippedRole {
                role: "effect".to_string(),
                domain_binding: "one named artifact or test result".to_string(),
                preserved_relation: "The governed effect applies to the allocated resource.".to_string(),
            },
        ],
        construction: ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes: vec![
                shared_node(
                    "ResourceRegistry",
                    "formal-example-structures::resource_registry::ResourceRegistry",
                    "Publish the exact job and partition identity set.",
                ),
                shared_node(
                    "RelationshipGraph",
                    "formal-example-structures::relationship_graph::RelationshipGraph",
                    "Commit the declared directed dependency relation.",
                ),
                shared_node(
                    "TraversalEngine",
                    "formal-example-structures::traversal::TraversalEngine",
                    "Visit every job reachable from the workflow root.",
                ),
                shared_node(
                    "StepGraph",
                    "formal-example-structures::step_graph::StepGraph",
                    "Own outer job readiness, running, and completion state.",
                ),
                shared_node(
                    "ForkJoin",
                    "formal-example-structures::fork_join::ForkJoin",
                    "Own test-worker lifecycle, barrier, and joined-output state.",
                ),
                shared_node(
                    "Budget<Compute>",
                    "formal-example-structures::budget::Budget<Compute>",
                    "Bound aggregate work while a separate identity check requires every debit.",
                ),
                shared_node(
                    "ActuationPass",
                    "formal-example-structures::actuation::ActuationPass",
                    "Apply each completed unit to its allocated output resource.",
                ),
                node(
                    "pipeline-binding",
                    ConstructionStratum::Connective,
                    "formal-example-domains::cicd::{execute_schedule,verify_run}",
                    "Bind the declared graph, nested carrier handoff, debit identities, and effect targets.",
                ),
                node(
                    "checked-host",
                    ConstructionStratum::Runtime,
                    "Rust::Vec+BTreeMap+BTreeSet+checked-u64",
                    "Provide finite storage, deterministic identity order, and checked indexing.",
                ),
            ],
            edges: vec![
                edge(
                    "checked-host",
                    "ResourceRegistry",
                    "Validated immutable identities enter one authoritative registry.",
                ),
                edge(
                    "ResourceRegistry",
                    "RelationshipGraph",
                    "Only registered job identities can be dependency endpoints.",
                ),
                edge(
                    "RelationshipGraph",
                    "TraversalEngine",
                    "The committed relation supplies the reachable-job frontier.",
                ),
                edge(
                    "RelationshipGraph",
                    "StepGraph",
                    "The declared edge set is bound exactly to the outer carrier edge set.",
                ),
                edge(
                    "StepGraph",
                    "ForkJoin",
                    "Starting the test job opens its nested worker epoch.",
                ),
                edge(
                    "ForkJoin",
                    "StepGraph",
                    "The test job completes only after joined output publication.",
                ),
                edge(
                    "ForkJoin",
                    "Budget<Compute>",
                    "Each completed test worker contributes its declared debit.",
                ),
                edge(
                    "StepGraph",
                    "Budget<Compute>",
                    "Each noncontainer outer job contributes its declared debit.",
                ),
                edge(
                    "Budget<Compute>",
                    "ActuationPass",
                    "A successful debit precedes its named output effect.",
                ),
                edge(
                    "ActuationPass",
                    "pipeline-binding",
                    "Recorded targets and outputs enter the composition verdict.",
                ),
            ],
            execution_carrier: "one outer StepGraph with one nested ForkJoin; Sequential appears only in the flattening control".to_string(),
            governed_commit_points: s(&[
                "identity registry commit",
                "dependency graph commit",
                "outer node completion",
                "worker completion",
                "join barrier",
                "joined output publication",
                "compute debit",
                "target-bound effect",
            ]),
            permitted_host_material: s(&[
                "finite vectors, maps, and sets",
                "static job and partition label projection",
                "checked index and integer operations",
                "trace serialization and error propagation",
            ]),
            scope_delta: Vec::new(),
            candidate_assessment: None,
        },
        relies: s(&[
            "The registered workflow models successful jobs only; a completed predecessor satisfies its outgoing dependencies.",
            "The workflow declaration and test partition set are immutable during one run.",
            "The source documentation is authoritative for the selected dependency and matrix semantics.",
            "The Rust host provides ordinary single-process memory safety for the bounded witness.",
        ]),
        oracle: Some(oracle),
        controls: vec![
            control(
                "FEX-CTRL-CICD-EARLY-EXECUTION",
                ControlClass::Construction,
                "StepGraph dependency release",
                "Move package start immediately after compile completion.",
                "StepGraph rejects the package start because both declared predecessors have not completed.",
                &["registry exactness", "declaration graph"],
            ),
            control(
                "FEX-CTRL-CICD-MISSING-PREDECESSOR",
                ControlClass::Construction,
                "RelationshipGraph -> StepGraph",
                "Omit the test-matrix to package edge from the carrier while retaining it in the declaration.",
                "The independent edge-set binding rejects the carrier even when the chosen schedule and final outputs remain green.",
                &["final output set", "outer completion"],
            ),
            control(
                "FEX-CTRL-CICD-SKIP-JOIN",
                ControlClass::Construction,
                "ForkJoin -> StepGraph",
                "Publish the test result and complete the outer test node without crossing the shared barrier.",
                "The nested carrier terminal-state and trace checks reject the run.",
                &["outer dependency order", "worker effects"],
            ),
            control(
                "FEX-CTRL-CICD-DROP-WORKER",
                ControlClass::Construction,
                "ForkJoin complete worker set",
                "Suppress one worker lifecycle while fabricating its public result.",
                "The authoritative worker state and exact debit checks reject the run.",
                &["final output set", "other worker completion"],
            ),
            control(
                "FEX-CTRL-CICD-FLATTEN-SEQUENTIAL",
                ControlClass::Construction,
                "StepGraph and ForkJoin carrier presence",
                "Replay a valid event order through Sequential alone.",
                "The output stays equal while the carrier binding rejects the missing StepGraph and ForkJoin.",
                &["final output set", "compute debit identity", "effect identity"],
            ),
            control(
                "FEX-CTRL-CICD-BYPASS-DEBIT",
                ControlClass::Construction,
                "Budget<Compute> -> ActuationPass",
                "Create the package output without charging its declared compute unit.",
                "The independent per-unit debit identity rejects the green capacity ledger.",
                &["package output", "capacity ceiling"],
            ),
            control(
                "FEX-CTRL-CICD-MISDIRECT-EFFECT",
                ControlClass::Construction,
                "Budget<Compute> -> ActuationPass",
                "Apply the static-analysis completion to the package output resource.",
                "The logical-to-actual target identity check rejects the run.",
                &["compute debit identity", "outer completion"],
            ),
        ],
        relation: None,
        boundary: ClaimBoundary {
            claim: claim.to_string(),
            claim_ceiling: claim_ceiling.to_string(),
            residuals: s(&[
                "The evidence covers one immutable successful four-job workflow and two required test partitions.",
                "The compute Budget is a total-work bound, not a runner-pool or wall-clock concurrency model.",
                "Conditional jobs, failures, retries, caching, deployment, product conformance, arbitrary graphs, and performance are excluded.",
            ]),
            falsifiers: s(&[
                "The plain-state and carrier-derived accepted schedule sets differ.",
                "An accepted schedule omits a declared output or completes a job before its predecessors.",
                "A registered control passes the construction verifier.",
                "The nested worker barrier cannot be bound to the outer test-node completion without unclassified generic behavior.",
            ]),
        },
    }
}

fn relation_record() -> DacBaseRecord {
    let lod_evidence_identity =
        evidence_content_identity(&lod_record()).expect("LOD evidence record serializes");
    let ospf_evidence_identity =
        evidence_content_identity(&ospf_record()).expect("OSPF evidence record serializes");
    let mut nodes = rooted_frontier_nodes();
    nodes.push(node(
        "relation-predicate",
        ConstructionStratum::Connective,
        "formal-example-domains::relation::compare",
        "Erase domain payloads and compare the registered node, edge, and implementation identities.",
    ));
    let mut edges = rooted_frontier_edges();
    edges.push(edge(
        "AllocationSnapshot",
        "relation-predicate",
        "Only completed green member traces enter the correspondence predicate.",
    ));
    let shared_nodes = s(&[
        "QualityHierarchy",
        "TraversalEngine",
        "CompetitiveSelection",
        "AllocationSnapshot",
    ]);
    let members = s(&["FEX-DOM-REN-03", "FEX-OSPF-001"]);
    let mut implementation_bindings = Vec::new();
    for member in &members {
        for shared in rooted_frontier_nodes() {
            implementation_bindings.push(SharedImplementationBinding {
                member_id: member.clone(),
                node_id: shared.id,
                implementation_identity: shared.implementation_identity,
                claim_path: if member == "FEX-DOM-REN-03" {
                    "formal-example-domains::lod::run_lod -> formal-example-structures::rooted_frontier::run_bounded_frontier"
                } else {
                    "formal-example-domains::ospf::run_ospf -> formal-example-structures::rooted_frontier::run_minimum_frontier"
                }
                .to_string(),
            });
        }
    }
    DacBaseRecord {
        id: "FEX-XFER-LOD-OSPF-01".to_string(),
        name: "LOD/OSPF structural correspondence".to_string(),
        family: ArtifactFamily::CrossExampleRelation,
        evidence_role: EvidenceRole::CrossExampleRelation,
        territory: TerritoryRecord {
            authorities: vec![
                source(
                    "FEX-DOM-REN-03",
                    AuthorityKind::ExecutableAuthority,
                    "formal-example-domains::lod::run_lod",
                    &lod_evidence_identity,
                    "Green bounded LOD member trace and independent domain result.",
                ),
                source(
                    "FEX-OSPF-001",
                    AuthorityKind::ExecutableAuthority,
                    "formal-example-domains::ospf::run_ospf",
                    &ospf_evidence_identity,
                    "Green bounded route-selection member trace and independent domain result.",
                ),
                source(
                    "FEX-SRC-THEORY-DAC",
                    AuthorityKind::ProjectDecomposition,
                    "docs/domain-abstraction-collapse.md Sections 1.6, 2.5, and 8.1",
                    "repository publication edition",
                    "Method donor for payload erasure and the proposed rendering/routing relation.",
                ),
            ],
            included_behavior: s(&[
                "Compare the load-bearing rooted-frontier stage in two green member results.",
                "Require exact shared nodes, ordered edges, and executable implementation identities.",
            ]),
            omissions: s(&[
                "Domain measures and cut policies are not equated.",
                "The full LOD and OSPF traces are not declared identical.",
                "OSPF-only source and conventional machinery remains unmatched.",
            ]),
        },
        native_problem: NativeProblemRecord {
            actors: s(&["LOD member", "route-selection member", "registered relation"]),
            state: s(&["two completed typed traces", "shared-subgraph contract"]),
            transitions: s(&[
                "erase domain payloads",
                "resolve member nodes to implementation identities",
                "compare ordered shared edges",
                "report unmatched roles",
            ]),
            commitments: s(&["one class-bounded relation verdict"]),
            inputs: s(&["green member results", "registered relation contract"]),
            outputs: s(&["shared nodes and edges", "unmatched nodes and residuals", "pass or fail"]),
            failures: s(&[
                "member result is not green",
                "node or edge mismatch",
                "implementation identity mismatch",
                "relation control stays green",
            ]),
            obligations: s(&[
                "nonempty shared graph",
                "exact member-node binding",
                "load-bearing edge use",
                "complete residual report",
            ]),
        },
        stripped_roles: s(&[
            "context",
            "target",
            "candidate",
            "extension",
            "measure",
            "frontier",
            "cut-policy",
            "snapshot",
        ])
        .into_iter()
        .map(|role| StrippedRole {
            domain_binding: format!("member-specific {role}"),
            preserved_relation: format!("Both members bind the neutral {role} role before payload erasure."),
            role,
        })
        .collect(),
        construction: ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes,
            edges,
            execution_carrier: "Sequential trace observation".to_string(),
            governed_commit_points: s(&[
                "member AllocationSnapshot.Commit",
                "relation verdict commit",
            ]),
            permitted_host_material: s(&[
                "BTreeSet for exact node comparison",
                "typed trace projection",
            ]),
            scope_delta: Vec::new(),
            candidate_assessment: None,
        },
        relies: s(&[
            "Both member runs pass their domain-result checks.",
            "Trace subjects distinguish the rooted-frontier stage from conventional machinery.",
            "Implementation identities name the same linked structure crate functions.",
        ]),
        oracle: None,
        controls: vec![control(
            "FEX-CTRL-XFER-LOD-OSPF-MISREGISTRATION",
            ControlClass::Relation,
            "registered member-node correspondence",
            "Add Budget -> RelationshipGraph as a false shared-node pair.",
            "The relation fails while both member domain results remain green.",
            &["LOD domain result", "OSPF domain result"],
        )],
        relation: Some(RelationContract {
            assurance_class: RelationAssuranceClass::SharedExecutableSubgraph,
            members,
            shared_nodes,
            shared_edges: rooted_frontier_edges(),
            implementation_bindings,
            relation_control_ids: s(&["FEX-CTRL-XFER-LOD-OSPF-MISREGISTRATION"]),
            member_edge_controls: vec![
                MemberEdgeControlBinding {
                    member_id: "FEX-DOM-REN-03".to_string(),
                    before: "QualityHierarchy".to_string(),
                    after: "TraversalEngine".to_string(),
                    control_id: "FEX-CTRL-LOD-DISCOVERY-BYPASS".to_string(),
                },
                MemberEdgeControlBinding {
                    member_id: "FEX-DOM-REN-03".to_string(),
                    before: "TraversalEngine".to_string(),
                    after: "CompetitiveSelection".to_string(),
                    control_id: "FEX-CTRL-LOD-SELECTION-BYPASS".to_string(),
                },
                MemberEdgeControlBinding {
                    member_id: "FEX-DOM-REN-03".to_string(),
                    before: "CompetitiveSelection".to_string(),
                    after: "AllocationSnapshot".to_string(),
                    control_id: "FEX-CTRL-LOD-SNAPSHOT-TRACE".to_string(),
                },
                MemberEdgeControlBinding {
                    member_id: "FEX-OSPF-001".to_string(),
                    before: "QualityHierarchy".to_string(),
                    after: "TraversalEngine".to_string(),
                    control_id: "FEX-CTRL-OSPF-DISCOVERY-BYPASS".to_string(),
                },
                MemberEdgeControlBinding {
                    member_id: "FEX-OSPF-001".to_string(),
                    before: "TraversalEngine".to_string(),
                    after: "CompetitiveSelection".to_string(),
                    control_id: "FEX-CTRL-OSPF-SELECTION-BYPASS".to_string(),
                },
                MemberEdgeControlBinding {
                    member_id: "FEX-OSPF-001".to_string(),
                    before: "CompetitiveSelection".to_string(),
                    after: "AllocationSnapshot".to_string(),
                    control_id: "FEX-CTRL-OSPF-SNAPSHOT".to_string(),
                },
            ],
        }),
        boundary: ClaimBoundary {
            claim: "Both examples invoke QualityHierarchy, TraversalEngine, CompetitiveSelection, and AllocationSnapshot in the same rooted-frontier order after domain payload erasure."
                .to_string(),
            claim_ceiling: "Shared-executable-subgraph reuse across the named bounded member claim paths."
                .to_string(),
            residuals: s(&[
                "Budget<Bytes> is specific to LOD.",
                "Candidate generation, measures, and cut policies remain domain-specific.",
                "RelationshipGraph, ResourceRegistry, and Reduction remain specific to route selection.",
                "View utility is not equated with path cost or routing semantics.",
            ]),
            falsifiers: s(&[
                "Either member bypasses the registered rooted-frontier subject.",
                "Any shared node resolves to different executable implementation identities.",
                "Any member bypasses a shared edge without failing relation binding.",
                "The misregistration control passes.",
            ]),
        },
    }
}

pub fn registry() -> Result<EvidenceRegistry, String> {
    EvidenceRegistry::new(vec![
        RecordDefinition::Base(Box::new(lod_record())),
        RecordDefinition::Instance(Box::new(lod_assembly_delta())),
        RecordDefinition::Base(Box::new(ospf_record())),
        RecordDefinition::Base(Box::new(edf_record())),
        RecordDefinition::Base(Box::new(crdt_record())),
        RecordDefinition::Base(Box::new(rdp_record())),
        RecordDefinition::Base(Box::new(stm_record())),
        RecordDefinition::Base(Box::new(cicd_record("FEX-DOM-CICD-01"))),
        RecordDefinition::Base(Box::new(cicd_record("FEX-DOM-CICD-03"))),
        RecordDefinition::Base(Box::new(cicd_record("FEX-ASM-06"))),
        RecordDefinition::Base(Box::new(relation_record())),
    ])
}

pub fn describe(id: &str) -> Result<MaterializedDacRecord, String> {
    registry()?.materialize(id)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_registered_records_validate() {
        let registry = registry().expect("valid evidence registry");
        assert_eq!(registry.ids().len(), 11);
        for id in registry.ids() {
            let record = registry.materialize(&id).expect("materialized record");
            assert!(record.record.construction.outcome.supports_reconstruction());
        }
    }

    #[test]
    fn assembly_materializes_base_and_delta() {
        let record = describe("FEX-ASM-01").expect("assembly evidence");
        assert_eq!(record.inherited_from, vec!["FEX-DOM-REN-03"]);
        assert_eq!(record.record.id, "FEX-ASM-01");
        assert!(record
            .record
            .construction
            .nodes
            .iter()
            .any(|node| node.id == "assembly-report"));
        assert_eq!(record.record.controls.len(), 4);
        assert_eq!(
            record.record.oracle.expect("assembly oracle").id,
            "FEX-REF-LOD-ASSEMBLY-EXHAUSTIVE"
        );
        assert!(record
            .base_evidence_identity
            .expect("base identity")
            .starts_with("sha256:"));
    }

    #[test]
    fn relation_records_exact_shared_implementation_bindings() {
        let record = describe("FEX-XFER-LOD-OSPF-01").expect("relation evidence");
        let relation = record.record.relation.expect("relation contract");
        assert_eq!(relation.implementation_bindings.len(), 8);
        assert_eq!(relation.member_edge_controls.len(), 6);
        assert_eq!(
            relation.assurance_class,
            RelationAssuranceClass::SharedExecutableSubgraph
        );
    }

    #[test]
    fn relation_requires_every_member_control_for_every_shared_edge() {
        let mut relation = relation_record();
        relation
            .relation
            .as_mut()
            .expect("relation")
            .member_edge_controls
            .pop();
        let error = EvidenceRegistry::new(vec![
            RecordDefinition::Base(Box::new(lod_record())),
            RecordDefinition::Base(Box::new(ospf_record())),
            RecordDefinition::Base(Box::new(relation)),
        ])
        .expect_err("uncontrolled member edge must fail");
        assert!(error.contains("exact member-edge control binding"));
    }

    #[test]
    fn relation_binding_must_match_each_member_construction_account() {
        let mut relation = relation_record();
        for binding in &mut relation
            .relation
            .as_mut()
            .expect("relation")
            .implementation_bindings
        {
            if binding.node_id == "QualityHierarchy" {
                binding.implementation_identity = "fabricated::QualityHierarchy".to_string();
            }
        }
        let error = EvidenceRegistry::new(vec![
            RecordDefinition::Base(Box::new(lod_record())),
            RecordDefinition::Base(Box::new(ospf_record())),
            RecordDefinition::Base(Box::new(relation)),
        ])
        .expect_err("fabricated implementation identity must fail");
        assert!(error.contains("differs from the member construction account"));
    }

    #[test]
    fn equal_false_member_and_relation_identities_are_rejected() {
        let mut lod = lod_record();
        let mut ospf = ospf_record();
        let mut relation = relation_record();
        let false_identity = "formal-example-structures::missing::QualityHierarchy";
        for record in [&mut lod, &mut ospf] {
            record
                .construction
                .nodes
                .iter_mut()
                .find(|node| node.id == "QualityHierarchy")
                .expect("quality node")
                .implementation_identity = false_identity.to_string();
        }
        for binding in &mut relation
            .relation
            .as_mut()
            .expect("relation")
            .implementation_bindings
        {
            if binding.node_id == "QualityHierarchy" {
                binding.implementation_identity = false_identity.to_string();
            }
        }
        let error = EvidenceRegistry::new(vec![
            RecordDefinition::Base(Box::new(lod)),
            RecordDefinition::Base(Box::new(ospf)),
            RecordDefinition::Base(Box::new(relation)),
        ])
        .expect_err("matching false strings are not resolved source identities");
        assert!(error.contains("unresolved or wrong implementation identity"));
    }

    #[test]
    fn actual_reduction_operation_must_match_the_declared_caller() {
        use crate::{Check, ExampleRun};
        use formal_example_structures::{PathReduction, Reduction, TraceLog};
        let mut trace = TraceLog::default();
        let result =
            Reduction::fold([1u64, 2], 0, |a, b| a + b, &mut trace, "delivery").expect("fold");
        let mut run = ExampleRun {
            id: "FEX-DOM-DIST-01".to_string(),
            scenario: "operation binding".to_string(),
            output: result,
            reference: result,
            checks: vec![Check::pass("unchanged output", "3")],
            trace,
            residuals: Vec::new(),
        };
        assert!(run.passed(), "actual CRDT fold identity");
        let trace = std::mem::take(&mut run.trace);
        assert!(
            !run.passed(),
            "an erased trace provides no implementation binding"
        );
        run.trace = trace;
        let checks = std::mem::take(&mut run.checks);
        assert!(!run.passed(), "an empty check set is not admitted evidence");
        run.checks = checks;
        run.trace.emit(
            formal_example_structures::Structure::Budget,
            "Initialize",
            "delivery",
            "undeclared owner",
        );
        assert!(
            !run.passed(),
            "an undeclared emitted owner has no matching binding"
        );
        let mut comparison = TraceLog::default();
        PathReduction::compare(None, result, &mut comparison, "delivery");
        run.trace = comparison;
        assert!(
            !run.passed(),
            "same declared fold and result must reject a path comparison"
        );
        run.id = "FEX-OSPF-001".to_string();
        assert!(run.passed(), "actual OSPF comparison identity");
    }

    #[test]
    fn relation_edge_must_remain_inside_the_shared_node_set() {
        let mut relation = relation_record();
        relation.relation.as_mut().expect("relation").shared_edges[0].after =
            "relation-predicate".to_string();
        let error = EvidenceRegistry::new(vec![RecordDefinition::Base(Box::new(relation))])
            .expect_err("shared edge cannot leave shared nodes");
        assert!(error.contains("leaves the shared node set"));
    }

    #[test]
    fn inherited_record_rejects_a_stale_base_identity() {
        let mut delta = lod_assembly_delta();
        delta.base_evidence_identity = "sha256:stale".to_string();
        let error = EvidenceRegistry::new(vec![
            RecordDefinition::Base(Box::new(lod_record())),
            RecordDefinition::Instance(Box::new(delta)),
        ])
        .expect_err("stale base identity must fail");
        assert!(error.contains("base evidence identity does not match"));
    }

    #[test]
    fn inherited_record_applies_an_exact_rely_replacement() {
        let base = lod_record();
        let previous = base.relies[0].clone();
        let replacement = "Replacement rely for the assembly instance.".to_string();
        let mut delta = lod_assembly_delta();
        delta.added_relies.clear();
        delta
            .replaced_relies
            .push(formal_example_structures::RelyReplacement {
                previous: previous.clone(),
                replacement: replacement.clone(),
            });
        let registry = EvidenceRegistry::new(vec![
            RecordDefinition::Base(Box::new(base)),
            RecordDefinition::Instance(Box::new(delta)),
        ])
        .expect("exact rely replacement");
        let materialized = registry.materialize("FEX-ASM-01").expect("instance");
        assert!(!materialized.record.relies.contains(&previous));
        assert!(materialized.record.relies.contains(&replacement));
    }

    #[test]
    fn rely_replacements_resolve_only_against_the_base_record() {
        let base = lod_record();
        let previous = base.relies[0].clone();
        let intermediate = "Intermediate rely text.".to_string();
        let mut delta = lod_assembly_delta();
        delta.added_relies.clear();
        delta.replaced_relies = vec![
            formal_example_structures::RelyReplacement {
                previous,
                replacement: intermediate.clone(),
            },
            formal_example_structures::RelyReplacement {
                previous: intermediate,
                replacement: "Order-dependent replacement.".to_string(),
            },
        ];
        let error = EvidenceRegistry::new(vec![
            RecordDefinition::Base(Box::new(base)),
            RecordDefinition::Instance(Box::new(delta)),
        ])
        .expect_err("replacement cannot target text introduced by another replacement");
        assert!(error.contains("does not resolve exactly once"));
    }

    #[test]
    fn executable_result_record_requires_a_rely() {
        let mut record = lod_record();
        record.relies.clear();
        let error = EvidenceRegistry::new(vec![RecordDefinition::Base(Box::new(record))])
            .expect_err("empty relies must fail");
        assert!(error.contains("relies is empty"));
    }

    #[test]
    fn vocabulary_only_relation_is_rejected() {
        let mut record = relation_record();
        record.relation.as_mut().expect("relation").assurance_class =
            RelationAssuranceClass::VocabularyResemblance;
        let error = EvidenceRegistry::new(vec![RecordDefinition::Base(Box::new(record))])
            .expect_err("vocabulary-only relation must fail");
        assert!(error.contains("vocabulary resemblance"));
    }

    #[test]
    fn independent_result_records_reject_shared_oracle_imports() {
        let mut record = lod_record();
        record
            .oracle
            .as_mut()
            .expect("oracle")
            .imports_shared_structures = true;
        let error = EvidenceRegistry::new(vec![RecordDefinition::Base(Box::new(record))])
            .expect_err("dependent oracle must fail");
        assert!(error.contains("not independent"));
    }

    #[test]
    fn unclassified_recipe_endpoint_is_rejected() {
        let mut record = lod_record();
        record.construction.edges.push(edge(
            "QualityHierarchy",
            "missing-node",
            "invalid endpoint",
        ));
        let error = EvidenceRegistry::new(vec![RecordDefinition::Base(Box::new(record))])
            .expect_err("unclassified recipe endpoint must fail");
        assert!(error.contains("unclassified node"));
    }
}
