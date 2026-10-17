pub mod cicd;
pub mod cicd_reference;
pub mod crdt;
pub mod crdt_reference;
pub mod edf;
pub mod evidence;
pub mod lod;
pub mod ospf;
pub mod rdp;
pub mod rdp_reference;
pub mod references;
pub mod relation;
pub mod stm;
pub mod stm_reference;

use formal_example_structures::TraceLog;
use serde::Serialize;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Check {
    pub name: String,
    pub passed: bool,
    pub detail: String,
}

impl Check {
    pub fn pass(name: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            passed: true,
            detail: detail.into(),
        }
    }

    pub fn verdict(name: impl Into<String>, passed: bool, detail: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            passed,
            detail: detail.into(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ExampleRun<T> {
    pub id: String,
    pub scenario: String,
    pub output: T,
    pub reference: T,
    pub checks: Vec<Check>,
    pub trace: TraceLog,
    pub residuals: Vec<String>,
}

impl<T> ExampleRun<T> {
    pub fn passed(&self) -> bool {
        !self.checks.is_empty() && !self.trace.events().is_empty()
            && self.checks.iter().all(|check| check.passed)
            && evidence::describe(&self.id).is_ok_and(|record| {
                self.trace.events().iter().all(|event| {
                    let actual = event.structure.implementation_identity(Some(&event.action));
                    actual.is_some() && actual == event.implementation_identity
                        && record.record.construction.nodes.iter().any(|node| {
                            node.stratum == formal_example_structures::ConstructionStratum::Catalog
                                && (node.id == event.structure.name()
                                    || matches!((node.id.as_str(), node.implementation_identity.as_str(), event.structure),
                                        ("Budget<Bytes>", "formal-example-structures::budget::Budget<Bytes>", formal_example_structures::Structure::Budget)
                                        | ("Budget<Compute>", "formal-example-structures::budget::Budget<Compute>", formal_example_structures::Structure::Budget)))
                                && {
                            let declared = match node.implementation_identity.as_str() {
                                "formal-example-structures::budget::Budget<Bytes>"
                                | "formal-example-structures::budget::Budget<Compute>"
                                | "formal-example-structures::budget::Budget<ExecutionTicks>" =>
                                    "formal-example-structures::budget::Budget",
                                "formal-example-structures::resource_registry::ResourceRegistry<TaskSpec>" =>
                                    "formal-example-structures::resource_registry::ResourceRegistry",
                                "formal-example-structures::sequential::Sequential<Option<usize>>" =>
                                    "formal-example-structures::sequential::Sequential",
                                "formal-example-structures::selection::CompetitiveSelection::select_min_index" =>
                                    "formal-example-structures::selection::CompetitiveSelection",
                                identity => identity,
                            };
                            actual == Some(declared)
                                }
                        })
                })
            })
    }
}
