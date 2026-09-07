//! Data-pipeline workload (docs/execution-modalities.md).
//!
//! Linear chain: source -> map_0 -> map_1 -> ... -> sink. The operator
//! at each interior id applies one of the workload's i64 transforms.
//! The sink accumulates the records that reach it; `reduce` sums them.
//!
//! `compatible_modalities` returns all four (Sequential, ForkJoin,
//! StepGraph, StreamGraph). They form one equivalence class because
//! the reduce is associative and commutative (a sum) and the
//! transforms are pure functions on i64.

use std::collections::HashMap;

use crate::modalities::Modality;
use crate::workloads::{Operator, OperatorFactory, Workload};

pub type IntTransform = fn(i64) -> i64;

#[derive(Debug, Clone)]
pub struct DataPipelineWorkload {
    pub inputs: Vec<i64>,
    pub transforms: Vec<IntTransform>,
}

impl DataPipelineWorkload {
    pub fn new(inputs: Vec<i64>, transforms: Vec<IntTransform>) -> Self {
        Self { inputs, transforms }
    }

    /// Convenient default: 0..n with two transforms (+1, *2).
    pub fn default_with(n: usize) -> Self {
        let inputs: Vec<i64> = (0..n as i64).collect();
        let transforms: Vec<IntTransform> = vec![|x| x + 1, |x| x * 2];
        Self::new(inputs, transforms)
    }

    fn n_ops(&self) -> usize {
        self.transforms.len().max(1)
    }
}

/// Per-operator state: holds the transform to apply. Identity at op 0
/// when there are no transforms.
struct MapOp {
    f: Option<IntTransform>,
}

impl Operator<i64> for MapOp {
    fn on_record(&mut self, r: i64) -> Vec<i64> {
        match self.f {
            Some(f) => vec![f(r)],
            None => vec![r],
        }
    }
}

impl Workload for DataPipelineWorkload {
    type Record = i64;
    type Output = i64;
    type OpId = usize;

    fn operators(&self) -> Vec<(usize, OperatorFactory<i64>)> {
        let n = self.n_ops();
        let mut out: Vec<(usize, OperatorFactory<i64>)> = Vec::with_capacity(n);
        for i in 0..n {
            let f: Option<IntTransform> = self.transforms.get(i).copied();
            let factory: OperatorFactory<i64> = Box::new(move || Box::new(MapOp { f }));
            out.push((i, factory));
        }
        out
    }

    fn edges(&self) -> Vec<(usize, usize)> {
        let n = self.n_ops();
        (0..n.saturating_sub(1)).map(|i| (i, i + 1)).collect()
    }

    fn initial_inputs(&self) -> HashMap<usize, Vec<i64>> {
        let mut m: HashMap<usize, Vec<i64>> = HashMap::new();
        m.insert(0, self.inputs.clone());
        m
    }

    fn reduce(&self, sink_outputs: HashMap<usize, Vec<i64>>) -> i64 {
        let mut sum: i64 = 0;
        for (_id, recs) in sink_outputs {
            for r in recs {
                sum += r;
            }
        }
        sum
    }

    fn compatible_modalities(&self) -> &'static [Modality] {
        &[
            Modality::Sequential,
            Modality::ForkJoin,
            Modality::StepGraph,
            Modality::StreamGraph,
        ]
    }
}
