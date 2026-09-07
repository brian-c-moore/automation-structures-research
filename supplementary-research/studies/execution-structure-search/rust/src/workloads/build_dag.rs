//! Build-DAG workload (docs/execution-modalities.md).
//!
//! Reproduces Make and Bazel. The build graph is a DAG of named
//! nodes; each node declares a list of named inputs and a pure
//! transform from input contents to output content. Source nodes
//! (those with no incoming edges) are seeded with their declared
//! contents; intermediate and target nodes apply their transform to
//! the contents arriving from predecessors.
//!
//! The diamond shape it models:
//!     src.c
//!     header.h  --+--> compile --> link --> bin
//!     other.c   --+
//!
//! `compile` has three predecessor edges; the step/sequential drivers
//! must deliver all three contents before the transform runs.
//!
//! Modality: Sequential + StepGraph (single equivalence class); the
//! dispatcher uses cross-modal output comparison as the equivalence
//! check, so `trace_properties` is empty. `cv.dependencies = Fixed`
//! corresponds to Make, `Conditional` (content-hash) corresponds to
//! Bazel; both produce identical build output for identical inputs,
//! so the distinction is only observable through the policy axis,
//! not through the workload's output.

use std::collections::{BTreeMap, HashMap};

use crate::modalities::Modality;
use crate::policies::ConfigVector;
use crate::workloads::{Operator, OperatorFactory, Workload};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildRecord {
    /// The name of the node that emitted this record. Used by
    /// downstream collectors to reorder records into the declared
    /// input order before applying the transform.
    pub from: String,
    pub content: String,
}

#[derive(Debug, Clone)]
pub struct BuildNode {
    pub name: String,
    /// Names of the predecessor nodes (source files or other nodes)
    /// in the order this node's `transform` expects.
    pub inputs: Vec<String>,
    /// Pure function of the contents of `inputs`, in declared order.
    pub transform: fn(Vec<String>) -> String,
}

#[derive(Debug, Clone)]
pub struct BuildDagWorkload {
    /// Source-file contents keyed by file name. These names appear
    /// as `BuildNode::inputs` entries on the nodes that consume them.
    pub source_contents: BTreeMap<String, String>,
    /// Intermediate and target build nodes keyed by node name.
    pub nodes: BTreeMap<String, BuildNode>,
    /// The sink node whose content is the reduce output.
    pub target: String,
}

impl BuildDagWorkload {
    pub fn new(
        source_contents: BTreeMap<String, String>,
        nodes: BTreeMap<String, BuildNode>,
        target: String,
    ) -> Self {
        Self {
            source_contents,
            nodes,
            target,
        }
    }

    /// Diamond build: three source files feed `compile`, `compile`
    /// feeds `link`, `link` feeds `bin`. `bin` is the target.
    pub fn small_example() -> Self {
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
        sources.insert("src.c".to_string(), "code1".to_string());
        sources.insert("header.h".to_string(), "code2".to_string());
        sources.insert("other.c".to_string(), "code3".to_string());
        Self {
            source_contents: sources,
            nodes,
            target: "bin".to_string(),
        }
    }
}

/// Source-file operator: passes records straight through. The
/// initial_inputs seed already tags records with the source's `from`
/// name, so downstream collectors can identify them.
struct SourceOp;

impl Operator<BuildRecord> for SourceOp {
    fn on_record(&mut self, r: BuildRecord) -> Vec<BuildRecord> {
        vec![r]
    }
}

/// Build-node operator: collects records keyed by `from`, applies
/// the declared transform in declared input order at end-of-stream,
/// emits a single record tagged with this node's name.
struct BuildOp {
    name: String,
    declared_inputs: Vec<String>,
    transform: fn(Vec<String>) -> String,
    collected: HashMap<String, String>,
}

impl Operator<BuildRecord> for BuildOp {
    fn on_record(&mut self, r: BuildRecord) -> Vec<BuildRecord> {
        self.collected.insert(r.from, r.content);
        Vec::new()
    }

    fn on_end_of_stream(&mut self) -> Vec<BuildRecord> {
        let inputs: Vec<String> = self
            .declared_inputs
            .iter()
            .map(|i| {
                self.collected.remove(i).unwrap_or_else(|| {
                    panic!(
                        "build node `{}` missing predecessor `{}` at EOS",
                        self.name, i
                    )
                })
            })
            .collect();
        let content = (self.transform)(inputs);
        vec![BuildRecord {
            from: self.name.clone(),
            content,
        }]
    }
}

impl Workload for BuildDagWorkload {
    type Record = BuildRecord;
    type Output = String;
    type OpId = String;

    fn operators(&self) -> Vec<(String, OperatorFactory<BuildRecord>)> {
        let mut out: Vec<(String, OperatorFactory<BuildRecord>)> = Vec::new();
        for name in self.source_contents.keys() {
            let name_str = name.clone();
            let factory: OperatorFactory<BuildRecord> = Box::new(move || Box::new(SourceOp));
            out.push((name_str, factory));
        }
        for (name, node) in &self.nodes {
            let name_str = name.clone();
            let declared_inputs = node.inputs.clone();
            let transform = node.transform;
            let factory: OperatorFactory<BuildRecord> = Box::new(move || {
                Box::new(BuildOp {
                    name: name_str.clone(),
                    declared_inputs: declared_inputs.clone(),
                    transform,
                    collected: HashMap::new(),
                })
            });
            out.push((name.clone(), factory));
        }
        out
    }

    fn edges(&self) -> Vec<(String, String)> {
        let mut e: Vec<(String, String)> = Vec::new();
        for (name, node) in &self.nodes {
            for input in &node.inputs {
                e.push((input.clone(), name.clone()));
            }
        }
        e
    }

    fn initial_inputs(&self) -> HashMap<String, Vec<BuildRecord>> {
        let mut m = HashMap::new();
        for (name, content) in &self.source_contents {
            m.insert(
                name.clone(),
                vec![BuildRecord {
                    from: name.clone(),
                    content: content.clone(),
                }],
            );
        }
        m
    }

    fn reduce(&self, sink_outputs: HashMap<String, Vec<BuildRecord>>) -> String {
        sink_outputs
            .get(&self.target)
            .and_then(|recs| recs.first())
            .map(|r| r.content.clone())
            .unwrap_or_default()
    }

    fn compatible_modalities(&self) -> &'static [Modality] {
        &[Modality::Sequential, Modality::StepGraph]
    }

    fn equivalence_classes(&self) -> Vec<Vec<Modality>> {
        vec![vec![Modality::Sequential, Modality::StepGraph]]
    }

    fn trace_properties(&self, _cv: &ConfigVector) -> Vec<Box<dyn Fn(&String) -> bool>> {
        // Cross-modality comparison (Sequential vs StepGraph) is the
        // dispatcher's verification path for this workload; no extra
        // trace properties needed.
        Vec::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modalities::{run_sequential, run_step_graph};
    use crate::policies::ConfigVector;

    #[test]
    fn small_example_diamond_resolves_in_declared_input_order() {
        let w = BuildDagWorkload::small_example();
        let cv = ConfigVector::default();
        let seq = run_sequential(&w, &cv);
        assert_eq!(seq, "bin(link(compile(code1,code2,code3)))");
    }

    #[test]
    fn step_graph_and_sequential_agree_on_diamond() {
        let w = BuildDagWorkload::small_example();
        let cv = ConfigVector::default();
        let seq = run_sequential(&w, &cv);
        let step = run_step_graph(&w, &cv).expect("acyclic");
        assert_eq!(seq, step);
    }
}
