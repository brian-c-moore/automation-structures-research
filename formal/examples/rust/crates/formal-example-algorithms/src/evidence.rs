use formal_example_structures::{
    evidence_content_identity, ArtifactFamily, AuthorityKind, ClaimBoundary, ConstructionAccount,
    ConstructionEdge, ConstructionNode, ConstructionOutcome, ConstructionStratum, ControlClass,
    ControlRecord, DacBaseRecord, EvidenceRegistry, EvidenceRole, InstanceDelta,
    MaterializedDacRecord, NativeProblemRecord, OracleRecord, RecordDefinition, SourceAuthority,
    StrippedRole, TerritoryRecord,
};

struct AlgorithmEvidence {
    id: &'static str,
    name: &'static str,
    source_id: &'static str,
    source_locator: &'static str,
    source_edition: &'static str,
    source_scope: &'static str,
    module: &'static str,
    oracle_identity: &'static str,
    input: &'static str,
    output: &'static str,
    recurrence: &'static str,
}

const ALGORITHMS: [AlgorithmEvidence; 10] = [
    AlgorithmEvidence {
        id: "FEX-ALG-060",
        name: "Climbing Stairs",
        source_id: "FEX-SRC-ALG-060",
        source_locator: "https://leetcode.com/problems/climbing-stairs/",
        source_edition: "LeetCode problem 70, retrieved 2026-08-25",
        source_scope: "Count paths to step n using increments of one or two; the artifact contract also defines n=0 as one empty path.",
        module: "climbing_stairs",
        oracle_identity: "formal-example-algorithms::references::climbing_stairs",
        input: "A step count from zero through 45.",
        output: "The number of ordered one-step and two-step paths to the target step.",
        recurrence: "Seed steps zero and one with one path, then sum the two predecessor counts.",
    },
    AlgorithmEvidence {
        id: "FEX-ALG-061",
        name: "House Robber",
        source_id: "FEX-SRC-ALG-061",
        source_locator: "https://leetcode.com/problems/house-robber/",
        source_edition: "LeetCode problem 198, retrieved 2026-08-25",
        source_scope: "Maximize selected nonadjacent values; the artifact admits an empty list and bounds each of at most 100 values from zero through 400.",
        module: "house_robber",
        oracle_identity: "formal-example-algorithms::references::house_robber",
        input: "At most 100 house values from zero through 400.",
        output: "The maximum sum of a subset containing no adjacent positions.",
        recurrence: "For each prefix, reduce the skip and take alternatives by maximum.",
    },
    AlgorithmEvidence {
        id: "FEX-ALG-062",
        name: "Longest Increasing Subsequence",
        source_id: "FEX-SRC-ALG-062",
        source_locator: "https://leetcode.com/problems/longest-increasing-subsequence/",
        source_edition: "LeetCode problem 300, retrieved 2026-08-25",
        source_scope: "Return the length of a strictly increasing subsequence; the artifact contract also admits an empty list.",
        module: "longest_increasing_subsequence",
        oracle_identity: "formal-example-algorithms::references::longest_increasing_subsequence",
        input: "At most 2500 signed integer values.",
        output: "The maximum strictly increasing subsequence length.",
        recurrence: "Each position extends every smaller predecessor and the final state reduces all position lengths.",
    },
    AlgorithmEvidence {
        id: "FEX-ALG-063",
        name: "Coin Change",
        source_id: "FEX-SRC-ALG-063",
        source_locator: "https://leetcode.com/problems/coin-change/",
        source_edition: "LeetCode problem 322, retrieved 2026-08-25",
        source_scope: "Return the minimum count of reusable positive-denomination coins that reaches the amount, or -1.",
        module: "coin_change",
        oracle_identity: "formal-example-algorithms::references::coin_change",
        input: "A nonempty positive coin set and an amount from zero through 10000.",
        output: "The minimum coin count, or -1 when the amount is unreachable.",
        recurrence: "Each amount reduces reachable predecessor amounts plus one by minimum.",
    },
    AlgorithmEvidence {
        id: "FEX-ALG-064",
        name: "Word Break",
        source_id: "FEX-SRC-ALG-064",
        source_locator: "https://leetcode.com/problems/word-break/",
        source_edition: "LeetCode problem 139, retrieved 2026-08-25",
        source_scope: "Decide whether a string is a concatenation of reusable dictionary words; the artifact contract also admits empty text.",
        module: "word_break",
        oracle_identity: "formal-example-algorithms::references::word_break",
        input: "Text of at most 300 characters and a nonempty dictionary of nonempty words.",
        output: "A Boolean segmentation verdict.",
        recurrence: "Each prefix reduces earlier segmentable prefixes connected by a dictionary word using logical OR.",
    },
    AlgorithmEvidence {
        id: "FEX-ALG-065",
        name: "Unique Paths",
        source_id: "FEX-SRC-ALG-065",
        source_locator: "https://leetcode.com/problems/unique-paths/",
        source_edition: "LeetCode problem 62, retrieved 2026-08-25",
        source_scope: "Count right-and-down paths across a positive rectangular grid; the artifact restricts the dimension sum to 68 for its signed 64-bit result type.",
        module: "unique_paths",
        oracle_identity: "formal-example-algorithms::references::unique_paths",
        input: "Row and column counts from one through 100 whose sum is at most 68.",
        output: "The number of paths from the upper-left cell to the lower-right cell.",
        recurrence: "Boundary cells contain one path and interior cells sum the upper and left predecessors.",
    },
    AlgorithmEvidence {
        id: "FEX-ALG-066",
        name: "Longest Common Subsequence",
        source_id: "FEX-SRC-ALG-066",
        source_locator: "https://leetcode.com/problems/longest-common-subsequence/",
        source_edition: "LeetCode problem 1143, retrieved 2026-08-25",
        source_scope: "Return the longest common subsequence length for two strings; the artifact contract also admits empty strings.",
        module: "longest_common_subsequence",
        oracle_identity: "formal-example-algorithms::references::longest_common_subsequence",
        input: "Two strings of at most 1000 characters each under the registered bounded cases.",
        output: "The longest common subsequence length.",
        recurrence: "Equal suffix characters extend the diagonal predecessor; unequal suffixes reduce the two shortened prefixes by maximum.",
    },
    AlgorithmEvidence {
        id: "FEX-ALG-067",
        name: "Edit Distance",
        source_id: "FEX-SRC-ALG-067",
        source_locator: "https://leetcode.com/problems/edit-distance/",
        source_edition: "LeetCode problem 72, retrieved 2026-08-25",
        source_scope: "Return unit-cost insertion, deletion, and replacement distance between two strings.",
        module: "edit_distance",
        oracle_identity: "formal-example-algorithms::references::edit_distance",
        input: "Two strings of at most 500 characters each under the registered bounded cases.",
        output: "The minimum permitted edit count.",
        recurrence: "Equal suffix characters retain the diagonal value; unequal suffixes reduce insert, delete, and replace predecessors by minimum plus one.",
    },
    AlgorithmEvidence {
        id: "FEX-ALG-068",
        name: "0/1 Knapsack",
        source_id: "FEX-SRC-ALG-068",
        source_locator: "https://users.ece.utexas.edu/~garg/publicCompanion/chapter10.html",
        source_edition: "University of Texas ECE dynamic-programming companion, retrieved 2026-08-25",
        source_scope: "Select indivisible items at most once to maximize value under capacity; the artifact bounds item count, weights, capacity, and the representable value sum.",
        module: "knapsack_01",
        oracle_identity: "formal-example-algorithms::references::knapsack_01",
        input: "At most 20 items with weights and capacity at most 200, nonnegative values, and a representable total value.",
        output: "The maximum admitted item value.",
        recurrence: "Each item-prefix and capacity state reduces skip and feasible take alternatives by maximum.",
    },
    AlgorithmEvidence {
        id: "FEX-ALG-069",
        name: "Longest Palindromic Subsequence",
        source_id: "FEX-SRC-ALG-069",
        source_locator: "https://leetcode.com/problems/longest-palindromic-subsequence/",
        source_edition: "LeetCode problem 516, retrieved 2026-08-25",
        source_scope: "Return the longest palindromic subsequence length; the artifact contract also admits empty text.",
        module: "longest_palindromic_subsequence",
        oracle_identity: "formal-example-algorithms::references::longest_palindromic_subsequence",
        input: "Text of at most 1000 characters under the registered bounded cases.",
        output: "The longest palindromic subsequence length.",
        recurrence: "Matching span endpoints extend the inner span; unequal endpoints reduce the two shortened spans by maximum.",
    },
];

fn strings(values: &[&str]) -> Vec<String> {
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
    identity: &str,
    responsibility: &str,
) -> ConstructionNode {
    ConstructionNode {
        id: id.to_string(),
        stratum,
        implementation_identity: identity.to_string(),
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
        adjacent_checks: strings(adjacent_checks),
    }
}

fn memoization_roles() -> Vec<StrippedRole> {
    [
        (
            "state",
            "one admitted dynamic-programming subproblem",
            "Names one result that may be computed and stored once.",
        ),
        (
            "dependency",
            "a predecessor subproblem required by a recurrence",
            "Must commit before the dependent state is evaluated.",
        ),
        (
            "candidate",
            "one recurrence alternative derived from stored predecessors",
            "Contributes one value to the declared reduction.",
        ),
        (
            "reduction",
            "the algorithm-specific sum, minimum, maximum, or logical OR",
            "Combines recurrence candidates under one declared operation.",
        ),
        (
            "stored-result",
            "the committed value for one state ID",
            "Cannot replace an already stored state result.",
        ),
        (
            "result",
            "the designated terminal state",
            "Projects one stored state as the algorithm output.",
        ),
    ]
    .into_iter()
    .map(|(role, binding, relation)| StrippedRole {
        role: role.to_string(),
        domain_binding: binding.to_string(),
        preserved_relation: relation.to_string(),
    })
    .collect()
}

fn schema_record() -> DacBaseRecord {
    DacBaseRecord {
        id: "FEX-SC-C01".to_string(),
        name: "Memoization".to_string(),
        family: ArtifactFamily::ClassicalSchema,
        evidence_role: EvidenceRole::ReusableSchema,
        territory: TerritoryRecord {
            authorities: vec![
                source(
                    "FEX-SRC-ALGORITHM-DP",
                    AuthorityKind::PrimaryTextbook,
                    "https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/",
                    "Introduction to Algorithms, fourth edition, MIT Press, 2022",
                    "Dynamic-programming decomposition into overlapping subproblems with stored results.",
                ),
                source(
                    "FEX-SRC-ALGORITHM-REGISTRY",
                    AuthorityKind::ProjectDecomposition,
                    "supplementary-research/studies/domain-corpora/algorithms/rust/tests.toml",
                    "supplementary algorithm corpus donor",
                    "Registered Memoization recipe and the ten associated corpus witnesses.",
                ),
                source(
                    "FEX-SRC-STRUCTURE-AUTHORITIES",
                    AuthorityKind::ExecutableAuthority,
                    "formal/structures/{ResourceRegistry,TraversalEngine,Reduction}",
                    "current formal structure profiles",
                    "Catalog obligations used by the executable schema.",
                ),
            ],
            included_behavior: strings(&[
                "Finite dependency graphs with at least one root and one designated result state.",
                "A state is admitted once, evaluated after its dependencies, reduced once, and stored once.",
                "The designated output equals the stored recurrence result.",
            ]),
            omissions: strings(&[
                "Parallel evaluation, cache eviction, incremental invalidation, and persistence.",
                "Asymptotic performance and allocation bounds.",
            ]),
        },
        native_problem: NativeProblemRecord {
            actors: strings(&["subproblem scheduler", "result registry", "recurrence reducer"]),
            state: strings(&["finite subproblem definitions", "ready frontier", "stored results"]),
            transitions: strings(&[
                "admit dependency roots",
                "visit a ready state",
                "reduce recurrence candidates",
                "store the state result",
            ]),
            commitments: strings(&[
                "each state ID is stored at most once",
                "the designated result is returned only after all admitted states are stored",
            ]),
            inputs: strings(&["finite dependency nodes", "candidate derivation", "reduction operation"]),
            outputs: strings(&["designated stored result", "state-accounting totals", "structural trace"]),
            failures: strings(&[
                "missing dependency",
                "dependency cycle",
                "duplicate state ID",
                "empty reduction candidate set",
            ]),
            obligations: strings(&[
                "dependencies precede evaluation",
                "one result is stored per admitted state",
                "the declared reduction determines every stored result",
            ]),
        },
        stripped_roles: memoization_roles(),
        construction: ConstructionAccount {
            outcome: ConstructionOutcome::CatalogComposition,
            nodes: vec![
                node(
                    "memoization-composition",
                    ConstructionStratum::Connective,
                    "formal-example-structures::memoization::run_memoization",
                    "Schedule dependency-ready states and connect the three catalog obligations.",
                ),
                node(
                    "ResourceRegistry",
                    ConstructionStratum::Catalog,
                    "formal-example-structures::resource_registry::ResourceRegistry",
                    "Reject duplicate state definitions and duplicate stored results.",
                ),
                node(
                    "TraversalEngine",
                    ConstructionStratum::Catalog,
                    "formal-example-structures::traversal::TraversalEngine",
                    "Visit each ready state and complete only after the frontier empties.",
                ),
                node(
                    "Reduction",
                    ConstructionStratum::Catalog,
                    "formal-example-structures::reduction::Reduction",
                    "Combine every state's recurrence candidates under the supplied operation.",
                ),
                node(
                    "sequential-host",
                    ConstructionStratum::Runtime,
                    "Rust::Vec+BTreeMap+BTreeSet+checked-input-bounds",
                    "Provide deterministic finite storage and sequential execution.",
                ),
            ],
            edges: vec![
                edge(
                    "sequential-host",
                    "memoization-composition",
                    "The host supplies a finite state graph and deterministic storage.",
                ),
                edge(
                    "memoization-composition",
                    "ResourceRegistry",
                    "The composition registers definitions and stores state results by unique ID.",
                ),
                edge(
                    "ResourceRegistry",
                    "TraversalEngine",
                    "Registered dependency roots initialize topological traversal.",
                ),
                edge(
                    "TraversalEngine",
                    "Reduction",
                    "A state is visited only after all predecessor results are stored.",
                ),
                edge(
                    "Reduction",
                    "ResourceRegistry",
                    "The reduced recurrence value is stored once under the visited state ID.",
                ),
            ],
            execution_carrier: "Sequential".to_string(),
            governed_commit_points: strings(&[
                "ResourceRegistry.Store for each admitted state",
                "TraversalEngine.Complete after all admitted states are stored",
            ]),
            permitted_host_material: strings(&[
                "Vec for finite candidates and frontier storage",
                "BTreeMap and BTreeSet for deterministic identity lookup",
                "algorithm-specific pure candidate derivation",
            ]),
            scope_delta: Vec::new(),
            candidate_assessment: None,
        },
        relies: strings(&[
            "The dependency graph is finite and every non-root dependency names an admitted state.",
            "Candidate derivation is deterministic and has no side effects outside the supplied state registry.",
            "Registered input bounds prevent integer overflow in the tested result domain.",
            "The Sequential carrier runs one state transition at a time.",
        ]),
        oracle: Some(OracleRecord {
            id: "FEX-REF-MEMOIZATION-DIAMOND".to_string(),
            method: "Directly add the two fixture leaves without importing or calling the Memoization composition."
                .to_string(),
            implementation_identity:
                "formal-example-algorithms::references::memoization_fixture".to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: strings(&["two independent root values", "one dependent result"]),
            equivalence_relation: "Exact integer equality for the schema fixture.".to_string(),
            common_mode_risks: strings(&[
                "The construction and reference share the fixture's two integer inputs.",
                "The fixture exercises one dependency diamond rather than every recurrence shape.",
            ]),
        }),
        controls: vec![
            control(
                "FEX-CTRL-MEMO-REGISTRY-BYPASS",
                ControlClass::Construction,
                "ResourceRegistry -> TraversalEngine",
                "Move definition and result registration to a detached trace.",
                "The memoization-recipe verdict fails while the computed fixture value remains correct.",
                &["schema-reference-agreement", "state-accounting"],
            ),
            control(
                "FEX-CTRL-MEMO-TRAVERSAL-BYPASS",
                ControlClass::Construction,
                "TraversalEngine -> Reduction",
                "Evaluate ready states without the registered traversal engine.",
                "The memoization-recipe verdict fails while the computed fixture value remains correct.",
                &["schema-reference-agreement", "state-accounting"],
            ),
            control(
                "FEX-CTRL-MEMO-REDUCTION-BYPASS",
                ControlClass::Construction,
                "Reduction -> ResourceRegistry",
                "Fold recurrence candidates without emitting the registered Reduction transition.",
                "The memoization-recipe verdict fails while the computed fixture value remains correct.",
                &["schema-reference-agreement", "state-accounting"],
            ),
        ],
        relation: None,
        boundary: ClaimBoundary {
            claim: "Each admitted subproblem is computed once after its dependencies, and its stored result equals the registered predecessor reduction."
                .to_string(),
            claim_ceiling: "Bounded executable schema fixture under the finite Sequential carrier and registered controls."
                .to_string(),
            residuals: strings(&[
                "The reusable schema has no parametric deductive proof in this artifact.",
                "Instance fidelity is established separately for each registered algorithm.",
            ]),
            falsifiers: strings(&[
                "A state is stored more than once.",
                "A state is evaluated before one of its declared dependencies.",
                "A stored value differs from its declared candidate reduction.",
                "A schema bypass control leaves structural binding green.",
            ]),
        },
    }
}

fn instance_delta(definition: &AlgorithmEvidence, base_identity: &str) -> InstanceDelta {
    let recurrence_node = format!("{}-recurrence", definition.module.replace('_', "-"));
    InstanceDelta {
        id: definition.id.to_string(),
        name: definition.name.to_string(),
        family: ArtifactFamily::ClassicalAlgorithm,
        evidence_role: EvidenceRole::CorpusWitness,
        base_id: "FEX-SC-C01".to_string(),
        base_evidence_identity: base_identity.to_string(),
        territory: Some(TerritoryRecord {
            authorities: vec![
                source(
                    definition.source_id,
                    AuthorityKind::ProblemContract,
                    definition.source_locator,
                    definition.source_edition,
                    definition.source_scope,
                ),
                source(
                    "FEX-SRC-ALGORITHM-DP",
                    AuthorityKind::PrimaryTextbook,
                    "https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/",
                    "Introduction to Algorithms, fourth edition, MIT Press, 2022",
                    "Dynamic-programming method authority.",
                ),
                source(
                    "FEX-SRC-ALGORITHM-REGISTRY",
                    AuthorityKind::ProjectDecomposition,
                    "supplementary-research/studies/domain-corpora/algorithms/rust/tests.toml",
                    "supplementary algorithm corpus donor",
                    "Prior recipe and deterministic test material; this donor does not establish reconstruction or oracle independence.",
                ),
            ],
            included_behavior: strings(&[
                definition.input,
                definition.output,
                definition.recurrence,
            ]),
            omissions: strings(&[
                "Inputs outside the registered contract.",
                "Asymptotic optimality, wall-clock performance, and memory bounds.",
            ]),
        }),
        native_problem: Some(NativeProblemRecord {
            actors: strings(&[definition.name, "input provider", "result consumer"]),
            state: strings(&[definition.input, "admitted recurrence states", "stored state values"]),
            transitions: strings(&[
                "derive the finite recurrence graph",
                "evaluate dependency-ready states",
                "commit the designated result",
            ]),
            commitments: strings(&[definition.output, definition.recurrence]),
            inputs: strings(&[definition.input]),
            outputs: strings(&[definition.output]),
            failures: strings(&[
                "input violates the registered bound",
                "construction and reference differ",
                "schema binding fails",
            ]),
            obligations: strings(&[
                "exact result equality with the independent reference",
                "complete binding to the inherited Memoization schema",
            ]),
        }),
        stripped_roles: Some(memoization_roles()),
        added_nodes: vec![node(
            &recurrence_node,
            ConstructionStratum::Domain,
            &format!(
                "formal-example-algorithms::{}::{{build_problem,compose}}",
                definition.module
            ),
            definition.recurrence,
        )],
        assembly_seams: vec![edge(
            &recurrence_node,
            "memoization-composition",
            "The algorithm-specific recurrence supplies finite states, dependencies, candidates, and a reduction operation to the shared composition.",
        )],
        added_relies: strings(&[
            definition.input,
            "Generated cases use the registered deterministic generator and fixed seed.",
        ]),
        replaced_relies: Vec::new(),
        inherited_control_bindings: strings(&[
            "FEX-CTRL-MEMO-REGISTRY-BYPASS",
            "FEX-CTRL-MEMO-TRAVERSAL-BYPASS",
            "FEX-CTRL-MEMO-REDUCTION-BYPASS",
        ]),
        added_controls: vec![control(
            &format!("FEX-CTRL-{}-ORACLE", definition.id.trim_start_matches("FEX-")),
            ControlClass::Oracle,
            "algorithm-output -> independent-reference",
            "Corrupt the completed output after the Memoization composition returns.",
            "The output-reference verdict fails while memoization-recipe remains green.",
            &["memoization-recipe", "state-accounting"],
        )],
        oracle: Some(OracleRecord {
            id: format!("FEX-REF-{}", definition.id.trim_start_matches("FEX-")),
            method: format!(
                "A separately written reference computes the registered {} output without importing the shared structure crate or calling the construction module.",
                definition.name
            ),
            implementation_identity: definition.oracle_identity.to_string(),
            imports_shared_structures: false,
            calls_construction_helpers: false,
            expected_data: strings(&[
                "named source examples",
                "boundary cases",
                "1000 deterministic generated cases",
            ]),
            equivalence_relation: "Exact typed output equality for every registered case."
                .to_string(),
            common_mode_risks: strings(&[
                "The construction and reference share the public typed input contract.",
                "Some references use the same mathematical recurrence through separate storage and control code.",
            ]),
        }),
        boundary: ClaimBoundary {
            claim: format!(
                "Result matches the independent {} reference for every registered case in the bounded input domain.",
                match definition.id {
                    "FEX-ALG-060" => "climbing_stairs",
                    "FEX-ALG-061" => "house_robber",
                    "FEX-ALG-062" => "lis",
                    "FEX-ALG-063" => "coin_change",
                    "FEX-ALG-064" => "word_break",
                    "FEX-ALG-065" => "unique_paths",
                    "FEX-ALG-066" => "lcs",
                    "FEX-ALG-067" => "edit_distance",
                    "FEX-ALG-068" => "knapsack_01",
                    "FEX-ALG-069" => "lps",
                    _ => unreachable!("registered Memoization algorithm"),
                }
            ),
            claim_ceiling: format!(
                "Exact functional agreement and Memoization-schema binding for {} over named and deterministic generated cases.",
                definition.name
            ),
            residuals: strings(&[
                "No asymptotic optimality or production-performance claim is made.",
                "The executable result is bounded to the registered typed inputs and cases.",
            ]),
            falsifiers: strings(&[
                "Any registered case differs from the independent reference.",
                "Any admitted state is missing from the stored state registry.",
                "Any inherited Memoization bypass leaves structural binding green.",
                "The oracle fault leaves functional agreement green.",
            ]),
        },
    }
}

pub fn registry() -> Result<EvidenceRegistry, String> {
    let schema = schema_record();
    let base_identity = evidence_content_identity(&schema)?;
    let mut definitions = vec![RecordDefinition::Base(Box::new(schema))];
    definitions.extend(ALGORITHMS.iter().map(|definition| {
        RecordDefinition::Instance(Box::new(instance_delta(definition, &base_identity)))
    }));
    EvidenceRegistry::new(definitions)
}

pub fn describe(id: &str) -> Result<MaterializedDacRecord, String> {
    registry()?.materialize(id)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_memoization_records_validate() {
        let registry = registry().expect("valid Memoization evidence registry");
        assert_eq!(registry.ids().len(), 11);
        for id in registry.ids() {
            let record = registry.materialize(&id).expect("materialized record");
            assert!(record.record.construction.outcome.supports_reconstruction());
        }
    }

    #[test]
    fn every_algorithm_is_a_bound_schema_instance() {
        let registry = registry().expect("valid Memoization evidence registry");
        for id in crate::ALGORITHM_IDS {
            let record = registry.materialize(id).expect("algorithm evidence");
            assert_eq!(record.inherited_from, vec!["FEX-SC-C01"]);
            assert_eq!(record.record.family, ArtifactFamily::ClassicalAlgorithm);
            assert_eq!(record.record.evidence_role, EvidenceRole::CorpusWitness);
            assert_eq!(record.record.controls.len(), 4);
            assert!(record.record.construction.nodes.iter().any(|node| {
                node.stratum == ConstructionStratum::Domain
                    && node
                        .implementation_identity
                        .starts_with("formal-example-algorithms::")
            }));
        }
    }

    #[test]
    fn algorithm_delta_replaces_problem_and_source_territory() {
        let record = describe("FEX-ALG-068").expect("knapsack evidence");
        assert!(record
            .record
            .territory
            .authorities
            .iter()
            .any(|authority| authority.id == "FEX-SRC-ALG-068"));
        assert!(record
            .record
            .native_problem
            .outputs
            .iter()
            .any(|output| output.contains("maximum admitted item value")));
    }
}
