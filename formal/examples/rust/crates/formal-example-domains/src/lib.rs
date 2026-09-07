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
        self.checks.iter().all(|check| check.passed)
    }
}
