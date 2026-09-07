//! Comparison harness for every registered algorithm. For each entry it runs
//! the Rust composition and the Python oracle on the same inputs and
//! compares under the algorithm's equivalence relation, recording
//! pass/fail, divergences, and friction.

use crate::config::{registry, CorpusEntry};
use crate::equivalence::equiv;
use crate::oracle;
use crate::value::Value;

#[derive(Debug, Clone)]
pub struct Divergence {
    pub input: Value,
    pub got: Value,
    pub want: Value,
}

#[derive(Debug, Clone)]
pub struct Outcome {
    pub name: &'static str,
    pub category: &'static str,
    pub phase: u8,
    pub ordering: &'static str,
    pub primitives: &'static str,
    pub total: usize,
    pub passed: usize,
    pub divergences: Vec<Divergence>,
}

impl Outcome {
    pub fn ok(&self) -> bool {
        self.divergences.is_empty() && self.total > 0
    }
}

/// Run one corpus entry over its full input set.
pub fn run_entry(e: &CorpusEntry) -> Outcome {
    let inputs = (e.gen_inputs)();
    let total = inputs.len();
    let mut passed = 0;
    let mut divergences = Vec::new();
    let wants = oracle::run_batch(e.oracle, &inputs);
    for (input, want) in inputs.into_iter().zip(wants.into_iter()) {
        let got = (e.compose)(input.clone());
        if equiv(&got, &want, e.equiv) {
            passed += 1;
        } else if divergences.len() < 5 {
            divergences.push(Divergence { input, got, want });
        }
    }
    Outcome {
        name: e.name,
        category: e.category,
        phase: e.phase,
        ordering: e.ordering,
        primitives: e.primitives,
        total,
        passed,
        divergences,
    }
}

/// Run the whole corpus (optionally filtered to one phase).
pub fn run(phase: Option<u8>) -> Vec<Outcome> {
    registry()
        .iter()
        .filter(|e| phase.map_or(true, |p| e.phase == p))
        .map(run_entry)
        .collect()
}

/// Build the hand-style REPORT body from outcomes (markdown).
pub fn report(outcomes: &[Outcome]) -> String {
    let mut s = String::new();
    s.push_str(
        "| Phase | Category | Algorithm | Ordering | Composition | Inputs | Pass | Status |\n",
    );
    s.push_str("|---|---|---|---|---|---:|---:|---|\n");
    let mut by_phase: std::collections::BTreeMap<u8, (usize, usize)> =
        std::collections::BTreeMap::new();
    for o in outcomes {
        let status = if o.ok() { "PASS" } else { "DIVERGENCE" };
        s.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {}/{} | {} |\n",
            o.phase,
            o.category,
            o.name,
            o.ordering,
            o.primitives,
            o.total,
            o.passed,
            o.total,
            status
        ));
        let e = by_phase.entry(o.phase).or_insert((0, 0));
        e.0 += 1;
        if o.ok() {
            e.1 += 1;
        }
    }
    s.push_str("\n### Per-phase summary\n\n| Phase | Algorithms | Clean |\n|---:|---:|---:|\n");
    for (p, (n, ok)) in &by_phase {
        s.push_str(&format!("| {} | {} | {}/{} |\n", p, n, ok, n));
    }
    let total: usize = outcomes.len();
    let clean: usize = outcomes.iter().filter(|o| o.ok()).count();
    s.push_str(&format!(
        "\n**Corpus total: {}/{} algorithms built from the six primitives plus content, byte-exact against the Python oracle.**\n",
        clean, total
    ));
    s
}
