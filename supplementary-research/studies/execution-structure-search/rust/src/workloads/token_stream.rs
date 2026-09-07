//! Token stream workload (bounded study configuration).
//!
//! "A graph that processes tokens as they are produced, with possible
//! cycles for ReAct-style agent loops. LangGraph reproductions run
//! this. Verifies per-token streaming and dynamic graph mutation."

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Step {
    Reason(String),
    Act(String),
    Observe(String),
    Final(String),
}

pub struct TokenStream {
    pub script: Vec<Step>,
}

impl TokenStream {
    pub fn small_example() -> Self {
        Self {
            script: vec![
                Step::Reason("plan".into()),
                Step::Act("call_search".into()),
                Step::Observe("found_3_results".into()),
                Step::Reason("refine".into()),
                Step::Act("call_search".into()),
                Step::Observe("found_1_result".into()),
                Step::Reason("synthesize".into()),
                Step::Final("answer".into()),
            ],
        }
    }

    /// Step the agent loop until a Final is emitted. Returns the
    /// trace of step labels in order.
    pub fn run(&self) -> Vec<String> {
        let mut trace = Vec::new();
        for step in &self.script {
            match step {
                Step::Reason(s) => trace.push(format!("R:{}", s)),
                Step::Act(s) => trace.push(format!("A:{}", s)),
                Step::Observe(s) => trace.push(format!("O:{}", s)),
                Step::Final(s) => {
                    trace.push(format!("F:{}", s));
                    break;
                }
            }
        }
        trace
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_example_terminates_with_final() {
        let w = TokenStream::small_example();
        let trace = w.run();
        assert!(trace.last().unwrap().starts_with("F:"));
    }
}
