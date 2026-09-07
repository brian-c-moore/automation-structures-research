//! Demo binary: runs the data-pipeline workload across all four
//! modalities and prints a comparison row, demonstrating output
//! equivalence (docs/execution-modalities.md first criterion).

use execution_modalities::modalities::fork_join::run_fork_join_with_workers;
use execution_modalities::modalities::stream_graph::run_stream_graph_with_capacity;
use execution_modalities::policies::ConfigVector;
use execution_modalities::workloads::data_pipeline::DataPipelineWorkload;
use execution_modalities::{run_sequential, run_step_graph};

fn main() {
    let workload = DataPipelineWorkload::default_with(8);
    let cv = ConfigVector::default();

    let seq = run_sequential(&workload, &cv);
    let forkj = run_fork_join_with_workers(&workload, &cv, 4);
    let stepg = run_step_graph(&workload, &cv).expect("data_pipeline is acyclic");
    let streamg = run_stream_graph_with_capacity(&workload, &cv, 2);

    println!("workload: data_pipeline (n=8, transforms=[+1, *2])");
    println!("  Sequential   = {}", seq);
    println!("  ForkJoin     = {}", forkj);
    println!("  StepGraph    = {}", stepg);
    println!("  StreamGraph  = {}", streamg);

    assert_eq!(seq, forkj);
    assert_eq!(seq, stepg);
    assert_eq!(seq, streamg);

    println!("\nOutput equivalence: PASS");
}
