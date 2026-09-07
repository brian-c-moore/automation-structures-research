use crate::{Structure, StructureError, TraceLog};
use serde::Serialize;
use std::collections::BTreeSet;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct FrontierItem<T> {
    work_id: u64,
    payload: T,
}

impl<T> FrontierItem<T> {
    pub fn work_id(&self) -> u64 {
        self.work_id
    }

    pub fn payload(&self) -> &T {
        &self.payload
    }

    pub fn into_payload(self) -> T {
        self.payload
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TraversalEngine<T> {
    frontier: Vec<FrontierItem<T>>,
    visited: BTreeSet<u64>,
    accepted: BTreeSet<u64>,
    next_work_id: u64,
    subject: String,
}

impl<T> TraversalEngine<T> {
    pub fn new(root: T, trace: &mut TraceLog, subject: &str) -> Self {
        trace.emit(
            Structure::TraversalEngine,
            "Initialize",
            subject,
            "frontier=1",
        );
        Self {
            frontier: vec![FrontierItem {
                work_id: 0,
                payload: root,
            }],
            visited: BTreeSet::new(),
            accepted: BTreeSet::new(),
            next_work_id: 1,
            subject: subject.to_string(),
        }
    }

    pub fn frontier(&self) -> &[FrontierItem<T>] {
        &self.frontier
    }

    pub fn enqueue(&mut self, payload: T, trace: &mut TraceLog) -> u64 {
        let work_id = self.next_work_id;
        self.next_work_id += 1;
        self.frontier.push(FrontierItem { work_id, payload });
        trace.emit(
            Structure::TraversalEngine,
            "Enqueue",
            &self.subject,
            format!("work_id={work_id} frontier={}", self.frontier.len()),
        );
        work_id
    }

    pub fn visit_at(
        &mut self,
        index: usize,
        trace: &mut TraceLog,
    ) -> Result<FrontierItem<T>, StructureError> {
        if index >= self.frontier.len() {
            return Err(StructureError::new(format!(
                "frontier index {index} is out of range"
            )));
        }
        let item = self.frontier.remove(index);
        if !self.visited.insert(item.work_id) {
            return Err(StructureError::new(format!(
                "work item {} was visited twice",
                item.work_id
            )));
        }
        trace.emit(
            Structure::TraversalEngine,
            "Visit",
            &self.subject,
            format!("work_id={} frontier={}", item.work_id, self.frontier.len()),
        );
        Ok(item)
    }

    pub fn accept(&mut self, work_id: u64, trace: &mut TraceLog) -> Result<(), StructureError> {
        if !self.visited.contains(&work_id) {
            return Err(StructureError::new(format!(
                "work item {work_id} cannot be accepted before visit"
            )));
        }
        self.accepted.insert(work_id);
        trace.emit(
            Structure::TraversalEngine,
            "Accept",
            &self.subject,
            format!("work_id={work_id}"),
        );
        Ok(())
    }

    pub fn finish(self, trace: &mut TraceLog) -> Result<(), StructureError> {
        if !self.frontier.is_empty() {
            return Err(StructureError::new(format!(
                "traversal finished with {} queued work items",
                self.frontier.len()
            )));
        }
        if !self.accepted.is_subset(&self.visited) {
            return Err(StructureError::new(
                "accepted work is not a subset of visited work",
            ));
        }
        trace.emit(
            Structure::TraversalEngine,
            "Complete",
            &self.subject,
            format!(
                "visited={} accepted={}",
                self.visited.len(),
                self.accepted.len()
            ),
        );
        Ok(())
    }
}
