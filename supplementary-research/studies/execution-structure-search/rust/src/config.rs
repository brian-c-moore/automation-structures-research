//! Classification-record loader (bounded study configuration).
//!
//! TOML schema for a named classification record:
//!
//! ```toml
//! name = "Erlang"
//! tier = 1
//! modality = "StreamGraph"
//! evidence = "documented_behavior"
//!
//! [policies]
//! invocation = "Pattern"     # FIFO | Priority | Pattern | AgeWeighted | Continuous | Vsync | Message | Time | Demand_Pull | ...
//! topology = "RuntimeAddressable"
//! dependencies = "HotSwappable"
//! lifecycle = "Supervision"
//!
//! workload = "actor_message_exchange"
//!
//! [trace_properties]
//! no_record_loss = true
//! supervision_restarts_crashed = true
//!
//! citations = [
//!     "Armstrong (2003) — Making Reliable Distributed Systems",
//!     "Agha (1986) — Actors: A Model of Concurrent Computation",
//! ]
//! ```

use serde::Deserialize;
use std::path::Path;

#[derive(Debug, Clone, Deserialize)]
pub struct FrameworkConfig {
    pub name: String,
    pub tier: u8,
    pub modality: String,
    pub evidence: String,
    pub policies: Policies,
    pub workload: String,
    #[serde(default)]
    pub trace_properties: TraceProperties,
    #[serde(default)]
    pub citations: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Policies {
    pub invocation: String,
    #[serde(default = "default_entity_model")]
    pub entity_model: String,
    pub topology: String,
    pub dependencies: String,
    pub lifecycle: String,
}
fn default_entity_model() -> String {
    "AnonymousOperator".to_string()
}

#[derive(Debug, Clone, Default, Deserialize)]
pub struct TraceProperties {
    #[serde(default)]
    pub no_record_loss: bool,
    #[serde(default)]
    pub backpressure_correct: bool,
    #[serde(default)]
    pub predecessor_before_successor: bool,
    #[serde(default)]
    pub barrier_before_output: bool,
    #[serde(default)]
    pub supervision_restarts_crashed: bool,
    #[serde(default)]
    pub demand_pull_only_requested: bool,
    #[serde(default)]
    pub per_frame_rebuild: bool,
}

#[derive(Debug)]
pub enum LoadError {
    Io(std::io::Error),
    Parse(toml::de::Error),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Io(e) => write!(f, "io: {}", e),
            LoadError::Parse(e) => write!(f, "toml: {}", e),
        }
    }
}

impl FrameworkConfig {
    pub fn load(path: &Path) -> Result<Self, LoadError> {
        let s = std::fs::read_to_string(path).map_err(LoadError::Io)?;
        toml::from_str(&s).map_err(LoadError::Parse)
    }

    /// Validate the top-level controlled vocabularies. Policy strings
    /// are preserved classification data; the bounded harness supports
    /// only a documented projection of them.
    pub fn validate(&self) -> Result<(), String> {
        const MODALITIES: &[&str] = &[
            "Sequential",
            "ForkJoin",
            "StepGraph",
            "StepGraph_Cyclic",
            "StreamGraph",
        ];
        if !MODALITIES.contains(&self.modality.as_str()) {
            return Err(format!("unknown modality: {}", self.modality));
        }
        const EVIDENCE: &[&str] = &[
            "direct_comparison",
            "trace_equivalence",
            "behavioral_test",
            "documented_behavior",
        ];
        if !EVIDENCE.contains(&self.evidence.as_str()) {
            return Err(format!("unknown evidence type: {}", self.evidence));
        }
        Ok(())
    }
}
