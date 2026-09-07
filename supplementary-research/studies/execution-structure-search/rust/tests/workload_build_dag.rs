//! BuildDagWorkload integration tests.
//!
//! Coverage:
//!  - Diamond shape: three sources feed `compile`, which feeds
//!    `link`, which feeds `bin`. Both Sequential and StepGraph
//!    must resolve all three predecessor inputs in declared order.
//!  - Determinism: the same workload run twice (and across the two
//!    compatible modalities) produces identical output.
//!  - Proptest: random source contents do not break the
//!    Sequential-vs-StepGraph equivalence.

use execution_modalities::modalities::{run_sequential, run_step_graph};
use execution_modalities::policies::ConfigVector;
use execution_modalities::workloads::build_dag::{BuildDagWorkload, BuildNode};
use proptest::prelude::*;
use std::collections::BTreeMap;

fn diamond_with_contents(c1: &str, c2: &str, c3: &str) -> BuildDagWorkload {
    let mut nodes = BTreeMap::new();
    nodes.insert(
        "compile".to_string(),
        BuildNode {
            name: "compile".to_string(),
            inputs: vec![
                "src.c".to_string(),
                "header.h".to_string(),
                "other.c".to_string(),
            ],
            transform: |xs| format!("compile({})", xs.join(",")),
        },
    );
    nodes.insert(
        "link".to_string(),
        BuildNode {
            name: "link".to_string(),
            inputs: vec!["compile".to_string()],
            transform: |xs| format!("link({})", xs.join(",")),
        },
    );
    nodes.insert(
        "bin".to_string(),
        BuildNode {
            name: "bin".to_string(),
            inputs: vec!["link".to_string()],
            transform: |xs| format!("bin({})", xs.join(",")),
        },
    );
    let mut sources = BTreeMap::new();
    sources.insert("src.c".to_string(), c1.to_string());
    sources.insert("header.h".to_string(), c2.to_string());
    sources.insert("other.c".to_string(), c3.to_string());
    BuildDagWorkload::new(sources, nodes, "bin".to_string())
}

#[test]
fn diamond_resolves_to_expected_artifact_string() {
    let w = BuildDagWorkload::small_example();
    let cv = ConfigVector::default();
    let out = run_sequential(&w, &cv);
    assert_eq!(out, "bin(link(compile(code1,code2,code3)))");
}

#[test]
fn diamond_is_deterministic_across_repeated_runs() {
    let w = BuildDagWorkload::small_example();
    let cv = ConfigVector::default();
    let first = run_sequential(&w, &cv);
    let second = run_sequential(&w, &cv);
    let third = run_sequential(&w, &cv);
    assert_eq!(first, second);
    assert_eq!(second, third);
}

#[test]
fn step_graph_matches_sequential_on_diamond() {
    let w = BuildDagWorkload::small_example();
    let cv = ConfigVector::default();
    let seq = run_sequential(&w, &cv);
    let step = run_step_graph(&w, &cv).expect("diamond is acyclic");
    assert_eq!(seq, step);
}

proptest! {
    #[test]
    fn equivalence_under_random_source_contents(
        c1 in "[a-z0-9]{1,8}",
        c2 in "[a-z0-9]{1,8}",
        c3 in "[a-z0-9]{1,8}",
    ) {
        let w = diamond_with_contents(&c1, &c2, &c3);
        let cv = ConfigVector::default();
        let seq = run_sequential(&w, &cv);
        let step = run_step_graph(&w, &cv).expect("diamond is acyclic");
        prop_assert_eq!(&seq, &step);
        // The output should preserve all three source contents in
        // declared input order — catches any reorder, drop, or
        // duplicate.
        let expected =
            format!("bin(link(compile({},{},{})))", c1, c2, c3);
        prop_assert_eq!(seq, expected);
    }
}
