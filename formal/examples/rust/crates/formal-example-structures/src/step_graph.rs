use crate::{Structure, StructureError, TraceLog};
use automation_structures::{StepGraph as PublishedStepGraph, StepState as PublishedStepState};

#[derive(Clone, Copy)]
enum ReplayAction {
    BecomeReady(usize),
    Start(usize),
    Complete(usize),
}

/// Trace adapter over the published finite-index `StepGraph` carrier.
pub struct StepGraph {
    inner: PublishedStepGraph,
    num_nodes: usize,
    edges: Vec<(usize, usize)>,
    replay: Vec<ReplayAction>,
}

impl StepGraph {
    pub fn new(
        num_nodes: usize,
        edges: Vec<(usize, usize)>,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        let inner = PublishedStepGraph::new(num_nodes, edges.clone()).map_err(|error| {
            StructureError::new(format!(
                "published StepGraph rejected construction: {error}"
            ))
        })?;
        trace.emit(
            Structure::StepGraph,
            "Initialize",
            subject,
            format!("nodes={num_nodes} edges={}", edges.len()),
        );
        Ok(Self {
            inner,
            num_nodes,
            edges,
            replay: Vec::new(),
        })
    }

    pub fn num_nodes(&self) -> usize {
        self.num_nodes
    }

    pub fn edges(&self) -> &[(usize, usize)] {
        &self.edges
    }

    pub fn states(&self) -> Vec<u8> {
        self.inner
            .states()
            .iter()
            .map(|state| state_tag(*state))
            .collect()
    }

    pub fn state(&self, node: usize) -> Option<u8> {
        self.inner.state(node).map(state_tag)
    }

    pub fn predecessors_complete(&self, node: usize) -> bool {
        node < self.num_nodes
            && self
                .edges
                .iter()
                .filter(|&&(_, target)| target == node)
                .all(|&(source, _)| self.inner.state(source) == Some(PublishedStepState::Complete))
    }

    pub fn become_ready(
        &mut self,
        node: usize,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if !self.inner.become_ready(node) {
            return Err(StructureError::new(format!(
                "published StepGraph rejected BecomeReady for {node}"
            )));
        }
        self.replay.push(ReplayAction::BecomeReady(node));
        trace.emit(
            Structure::StepGraph,
            "BecomeReady",
            subject,
            format!("node={node}"),
        );
        Ok(())
    }

    pub fn start_running(
        &mut self,
        node: usize,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if !self.inner.start(node) {
            return Err(StructureError::new(format!(
                "published StepGraph rejected StartRunning for {node}"
            )));
        }
        self.replay.push(ReplayAction::Start(node));
        trace.emit(
            Structure::StepGraph,
            "StartRunning",
            subject,
            format!("node={node}"),
        );
        Ok(())
    }

    pub fn complete_node(
        &mut self,
        node: usize,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if !self.inner.complete(node) {
            return Err(StructureError::new(format!(
                "published StepGraph rejected CompleteNode for {node}"
            )));
        }
        self.replay.push(ReplayAction::Complete(node));
        trace.emit(
            Structure::StepGraph,
            "CompleteNode",
            subject,
            format!("node={node}"),
        );
        Ok(())
    }

    pub fn done_stuttering(
        &self,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if !self.inner.is_done() {
            return Err(StructureError::new(
                "published StepGraph is not at its all-completed state",
            ));
        }
        trace.emit(
            Structure::StepGraph,
            "Done",
            subject,
            format!("completed={}", self.num_nodes),
        );
        Ok(())
    }
}

impl Clone for StepGraph {
    fn clone(&self) -> Self {
        let mut inner = PublishedStepGraph::new(self.num_nodes, self.edges.clone())
            .expect("published StepGraph configuration must replay");
        for action in &self.replay {
            let accepted = match *action {
                ReplayAction::BecomeReady(node) => inner.become_ready(node),
                ReplayAction::Start(node) => inner.start(node),
                ReplayAction::Complete(node) => inner.complete(node),
            };
            assert!(accepted, "published StepGraph action log must replay");
        }
        Self {
            inner,
            num_nodes: self.num_nodes,
            edges: self.edges.clone(),
            replay: self.replay.clone(),
        }
    }
}

fn state_tag(state: PublishedStepState) -> u8 {
    match state {
        PublishedStepState::NotReady => 0,
        PublishedStepState::Ready => 1,
        PublishedStepState::Running => 2,
        PublishedStepState::Complete => 3,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_diamond_obeys_dependency_release() {
        let mut trace = TraceLog::default();
        let mut graph = StepGraph::new(
            4,
            vec![(0, 1), (0, 2), (1, 3), (2, 3)],
            &mut trace,
            "diamond",
        )
        .unwrap();
        assert_eq!(graph.states(), [1, 0, 0, 0]);
        assert!(graph.become_ready(1, &mut trace, "node-1").is_err());
        graph.start_running(0, &mut trace, "node-0").unwrap();
        graph.complete_node(0, &mut trace, "node-0").unwrap();
        graph.become_ready(1, &mut trace, "node-1").unwrap();
        graph.become_ready(2, &mut trace, "node-2").unwrap();
        graph.start_running(1, &mut trace, "node-1").unwrap();
        graph.complete_node(1, &mut trace, "node-1").unwrap();
        assert!(graph.become_ready(3, &mut trace, "node-3").is_err());
        graph.start_running(2, &mut trace, "node-2").unwrap();
        graph.complete_node(2, &mut trace, "node-2").unwrap();
        graph.become_ready(3, &mut trace, "node-3").unwrap();
        graph.start_running(3, &mut trace, "node-3").unwrap();
        graph.complete_node(3, &mut trace, "node-3").unwrap();
        graph.done_stuttering(&mut trace, "diamond").unwrap();
        assert_eq!(graph.states(), [3, 3, 3, 3]);
    }

    #[test]
    fn canonical_cycle_has_no_initial_ready_node() {
        let mut trace = TraceLog::default();
        let graph = StepGraph::new(2, vec![(0, 1), (1, 0)], &mut trace, "cycle").unwrap();
        assert_eq!(graph.states(), [0, 0]);
        assert!(graph.done_stuttering(&mut trace, "cycle").is_err());
    }
}
