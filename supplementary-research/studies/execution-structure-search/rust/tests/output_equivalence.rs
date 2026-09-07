//! Output equivalence (the execution-modality study first criterion).
//!
//! All four modalities produce the same output for the same input.

use execution_modalities::modalities::fork_join::run_fork_join_with_workers;
use execution_modalities::modalities::stream_graph::run_stream_graph_with_capacity;
use execution_modalities::policies::ConfigVector;
use execution_modalities::workloads::data_pipeline::DataPipelineWorkload;
use execution_modalities::{run_sequential, run_step_graph};
use proptest::prelude::*;

#[test]
fn small_input_equivalence() {
    let workload = DataPipelineWorkload::default_with(5);
    let cv = ConfigVector::default();
    let seq = run_sequential(&workload, &cv);
    let forkj = run_fork_join_with_workers(&workload, &cv, 3);
    let stepg = run_step_graph(&workload, &cv).expect("data_pipeline is acyclic");
    let streamg = run_stream_graph_with_capacity(&workload, &cv, 2);
    assert_eq!(seq, forkj);
    assert_eq!(seq, stepg);
    assert_eq!(seq, streamg);
}

proptest! {
    #[test]
    fn equivalence_under_random_inputs(
        inputs in proptest::collection::vec(-100i64..100, 0..16),
        workers in 1usize..6,
        capacity in 1usize..6,
    ) {
        let transforms: Vec<fn(i64) -> i64> = vec![|x| x + 1, |x| x * 2, |x| x - 3];
        let workload = DataPipelineWorkload::new(inputs.clone(), transforms);
        let cv = ConfigVector::default();
        let seq    = run_sequential(&workload, &cv);
        let forkj  = run_fork_join_with_workers(&workload, &cv, workers);
        let stepg  = run_step_graph(&workload, &cv).expect("data_pipeline is acyclic");
        let streamg = run_stream_graph_with_capacity(&workload, &cv, capacity);
        prop_assert_eq!(seq, forkj);
        prop_assert_eq!(seq, stepg);
        prop_assert_eq!(seq, streamg);
    }
}
