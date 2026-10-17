use crate::{Structure, StructureError, TraceLog};
use automation_structures::compositions::traversal_engine::TraversalEngine as CanonicalTraversal;
use automation_structures::connectives::counter::Counter;
use automation_structures::primitives::resource_registry::ResourceRegistry as CanonicalRegistry;
use serde::Serialize;

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

pub struct TraversalEngine<T> {
    work: CanonicalTraversal,
    pending: CanonicalRegistry<u64, FrontierItem<T>>,
    issued: Counter,
    subject: String,
}

impl<T> TraversalEngine<T> {
    /// Bind typed dynamic admissions to the published finite traversal engine.
    /// The caller derives the work ceiling from its finite input/search profile.
    pub fn new(
        root: T,
        candidate_ceiling: usize,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        if candidate_ceiling == 0 {
            return Err(StructureError::new(
                "traversal requires storage for its root",
            ));
        }
        let count = candidate_ceiling
            .checked_add(1)
            .ok_or_else(|| StructureError::new("traversal universe overflow"))?;
        let budget = u64::try_from(count)
            .ok()
            .and_then(|count| count.checked_mul(2))
            .ok_or_else(|| StructureError::new("traversal work account overflow"))?;
        let mut work = CanonicalTraversal::try_new(count, 0, budget)
            .map_err(|_| StructureError::new("traversal work storage refused"))?;
        let mut pending = CanonicalRegistry::new();
        pending
            .try_reserve_entries(candidate_ceiling)
            .map_err(|_| StructureError::new("traversal payload storage refused"))?;
        if !work.can_visit(0) {
            return Err(StructureError::new("traversal synthetic root refused"));
        }
        work.visit_node(0);
        let mut traversal = Self {
            work,
            pending,
            issued: Counter::new(0),
            subject: subject.to_owned(),
        };
        traversal.admit(root).map_err(|(error, _)| error)?;
        trace.emit(
            Structure::TraversalEngine,
            "Initialize",
            subject,
            "frontier=1",
        );
        Ok(traversal)
    }

    pub fn frontier(&self) -> &[(u64, FrontierItem<T>)] {
        &self.pending.entries
    }

    pub fn enqueue(
        &mut self,
        payload: T,
        trace: &mut TraceLog,
    ) -> Result<u64, (StructureError, T)> {
        let work_id = self.admit(payload)?;
        trace.emit(
            Structure::TraversalEngine,
            "Enqueue",
            &self.subject,
            format!("work_id={work_id} frontier={}", self.pending.entries.len()),
        );
        Ok(work_id)
    }

    fn admit(&mut self, payload: T) -> Result<u64, (StructureError, T)> {
        let work_id = self.issued.value();
        let Some(node) = usize::try_from(work_id)
            .ok()
            .and_then(|id| id.checked_add(1))
        else {
            return Err((
                StructureError::new("traversal work identity overflow"),
                payload,
            ));
        };
        if node >= self.work.num_nodes || !self.work.queue_contains(node) {
            return Err((
                StructureError::new("traversal candidate ceiling exhausted"),
                payload,
            ));
        }
        let mut issued = self.issued;
        if !issued.try_increment() {
            return Err((
                StructureError::new("traversal work identity exhausted"),
                payload,
            ));
        }
        self.pending
            .try_insert_unique(work_id, FrontierItem { work_id, payload })
            .map_err(|(reason, _, item)| {
                (
                    StructureError::new(format!("traversal admission refused: {reason:?}")),
                    item.payload,
                )
            })?;
        self.issued = issued;
        Ok(work_id)
    }

    pub fn visit_at(
        &mut self,
        index: usize,
        trace: &mut TraceLog,
    ) -> Result<FrontierItem<T>, StructureError> {
        let work_id = self
            .pending
            .entries
            .get(index)
            .map(|(id, _)| *id)
            .ok_or_else(|| {
                StructureError::new(format!("frontier index {index} is out of range"))
            })?;
        let node = usize::try_from(work_id)
            .ok()
            .and_then(|id| id.checked_add(1))
            .ok_or_else(|| StructureError::new("traversal work identity overflow"))?;
        if !self.work.can_visit(node) {
            return Err(StructureError::new(format!(
                "work item {work_id} cannot be visited"
            )));
        }
        self.work.visit_node(node);
        let (_, item) = self
            .pending
            .deregister_at(index)
            .ok_or_else(|| StructureError::new("traversal lost admitted payload custody"))?;
        trace.emit(
            Structure::TraversalEngine,
            "Visit",
            &self.subject,
            format!(
                "work_id={} frontier={}",
                item.work_id,
                self.pending.entries.len()
            ),
        );
        Ok(item)
    }

    pub fn accept(&mut self, work_id: u64, trace: &mut TraceLog) -> Result<(), StructureError> {
        let node = usize::try_from(work_id)
            .ok()
            .and_then(|id| id.checked_add(1))
            .ok_or_else(|| StructureError::new("traversal work identity overflow"))?;
        if !self.work.accepted_contains(node) {
            return Err(StructureError::new(format!(
                "work item {work_id} cannot be accepted before visit"
            )));
        }
        trace.emit(
            Structure::TraversalEngine,
            "Accept",
            &self.subject,
            format!("work_id={work_id}"),
        );
        Ok(())
    }

    pub fn finish(mut self, trace: &mut TraceLog) -> Result<(), StructureError> {
        if !self.pending.entries.is_empty() {
            return Err(StructureError::new(format!(
                "traversal finished with {} queued work items",
                self.pending.entries.len()
            )));
        }
        let issued = usize::try_from(self.issued.value())
            .map_err(|_| StructureError::new("traversal issued count overflow"))?;
        let first_unused = issued
            .checked_add(1)
            .ok_or_else(|| StructureError::new("traversal universe overflow"))?;
        for node in first_unused..self.work.num_nodes {
            if !self.work.can_skip(node) {
                return Err(StructureError::new(
                    "traversal inactive slot cannot be closed",
                ));
            }
            self.work.skip(node);
        }
        if !self.work.can_terminate() {
            return Err(StructureError::new(
                "traversal owner frontier remains pending",
            ));
        }
        self.work.terminate();
        trace.emit(
            Structure::TraversalEngine,
            "Complete",
            &self.subject,
            format!(
                "visited={} accepted={}",
                self.work
                    .visited_count()
                    .checked_sub(1)
                    .ok_or_else(|| StructureError::new("traversal root visit missing"))?,
                self.work
                    .accepted
                    .accumulated
                    .len()
                    .checked_sub(1)
                    .ok_or_else(|| StructureError::new("traversal root acceptance missing"))?
            ),
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arbitrary_visits_preserve_pending_order_and_move_nonclone_payloads(
    ) -> Result<(), StructureError> {
        struct Payload(u64);
        let mut trace = TraceLog::default();
        let mut traversal = TraversalEngine::new(Payload(9), 4, &mut trace, "typed")?;
        let first = traversal
            .enqueue(Payload(2), &mut trace)
            .map_err(|(error, _)| error)?;
        let last = traversal
            .enqueue(Payload(3), &mut trace)
            .map_err(|(error, _)| error)?;
        assert!(traversal.accept(first, &mut trace).is_err());
        assert!(traversal.accept(u64::MAX, &mut trace).is_err());
        assert!(traversal.visit_at(3, &mut trace).is_err());
        let selected = traversal.visit_at(1, &mut trace)?;
        assert_eq!(selected.work_id(), first);
        assert_eq!(selected.into_payload().0, 2);
        assert!(traversal.work.visited_contains(2));
        assert!(traversal.work.accepted_contains(2));
        assert!(!traversal.work.queue_contains(2));
        assert_eq!(
            traversal
                .frontier()
                .iter()
                .map(|(id, _)| *id)
                .collect::<Vec<_>>(),
            vec![0, last]
        );
        traversal.accept(first, &mut trace)?;
        assert_eq!(traversal.visit_at(1, &mut trace)?.into_payload().0, 3);
        assert_eq!(traversal.visit_at(0, &mut trace)?.into_payload().0, 9);
        traversal.finish(&mut trace)?;
        assert!(trace
            .events()
            .last()
            .is_some_and(|event| event.action == "Complete"));
        Ok(())
    }

    #[test]
    fn ceiling_refusal_returns_original_and_does_not_consume_identity() -> Result<(), StructureError>
    {
        let mut trace = TraceLog::default();
        let mut traversal = TraversalEngine::new(String::from("root"), 1, &mut trace, "ceiling")?;
        let before = traversal.issued.value();
        let refusal = traversal
            .enqueue(String::from("retained"), &mut trace)
            .err()
            .ok_or_else(|| StructureError::new("ceiling was not refused"))?;
        assert_eq!(refusal.1, "retained");
        assert_eq!(traversal.issued.value(), before);
        assert_eq!(traversal.frontier().len(), 1);
        assert!(traversal.finish(&mut trace).is_err());
        assert!(!trace
            .events()
            .iter()
            .any(|event| event.action == "Complete"));
        assert!(TraversalEngine::new(0, 0, &mut trace, "zero").is_err());
        assert!(TraversalEngine::new(0, usize::MAX, &mut trace, "overflow").is_err());
        Ok(())
    }
}
