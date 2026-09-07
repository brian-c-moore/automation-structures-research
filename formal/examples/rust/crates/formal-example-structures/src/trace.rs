use crate::StructureError;
use serde::Serialize;
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "PascalCase")]
pub enum Structure {
    ActuationPass,
    AllocationSnapshot,
    Budget,
    CompetitiveSelection,
    ForkJoin,
    QualityHierarchy,
    Reduction,
    RelationshipGraph,
    ResourceRegistry,
    Sequential,
    StepGraph,
    TraversalEngine,
}

impl Structure {
    pub fn name(self) -> &'static str {
        match self {
            Self::ActuationPass => "ActuationPass",
            Self::AllocationSnapshot => "AllocationSnapshot",
            Self::Budget => "Budget",
            Self::CompetitiveSelection => "CompetitiveSelection",
            Self::ForkJoin => "ForkJoin",
            Self::QualityHierarchy => "QualityHierarchy",
            Self::Reduction => "Reduction",
            Self::RelationshipGraph => "RelationshipGraph",
            Self::ResourceRegistry => "ResourceRegistry",
            Self::Sequential => "Sequential",
            Self::StepGraph => "StepGraph",
            Self::TraversalEngine => "TraversalEngine",
        }
    }

    pub fn implementation_identity(self) -> &'static str {
        match self {
            Self::ActuationPass => "formal-example-structures::actuation::ActuationPass",
            Self::AllocationSnapshot => "formal-example-structures::snapshot::AllocationSnapshot",
            Self::Budget => "formal-example-structures::budget::Budget",
            Self::CompetitiveSelection => {
                "formal-example-structures::selection::CompetitiveSelection"
            }
            Self::ForkJoin => "formal-example-structures::fork_join::ForkJoin",
            Self::QualityHierarchy => {
                "formal-example-structures::quality_hierarchy::QualityHierarchy"
            }
            Self::Reduction => "formal-example-structures::reduction::PathReduction",
            Self::RelationshipGraph => {
                "formal-example-structures::relationship_graph::RelationshipGraph"
            }
            Self::ResourceRegistry => {
                "formal-example-structures::resource_registry::ResourceRegistry"
            }
            Self::Sequential => "formal-example-structures::sequential::Sequential",
            Self::StepGraph => "formal-example-structures::step_graph::StepGraph",
            Self::TraversalEngine => "formal-example-structures::traversal::TraversalEngine",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct StructuralEvent {
    pub sequence: u64,
    pub structure: Structure,
    pub action: String,
    pub subject: String,
    pub detail: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RecipeEdge {
    pub before: Structure,
    pub before_action: &'static str,
    pub after: Structure,
    pub after_action: &'static str,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct TraceLog {
    events: Vec<StructuralEvent>,
}

impl TraceLog {
    pub fn emit(
        &mut self,
        structure: Structure,
        action: impl Into<String>,
        subject: impl Into<String>,
        detail: impl Into<String>,
    ) -> u64 {
        let sequence = self.events.len() as u64;
        self.events.push(StructuralEvent {
            sequence,
            structure,
            action: action.into(),
            subject: subject.into(),
            detail: detail.into(),
        });
        sequence
    }

    pub fn events(&self) -> &[StructuralEvent] {
        &self.events
    }

    pub fn structures(&self) -> BTreeSet<Structure> {
        self.events.iter().map(|event| event.structure).collect()
    }

    pub fn structures_for(&self, subject: &str) -> BTreeSet<Structure> {
        self.events
            .iter()
            .filter(|event| event.subject == subject)
            .map(|event| event.structure)
            .collect()
    }

    pub fn first_sequence(&self, structure: Structure, action: &str) -> Option<u64> {
        self.events
            .iter()
            .find(|event| event.structure == structure && event.action == action)
            .map(|event| event.sequence)
    }

    pub fn first_sequence_for(
        &self,
        structure: Structure,
        action: &str,
        subject: &str,
    ) -> Option<u64> {
        self.events
            .iter()
            .find(|event| {
                event.structure == structure && event.action == action && event.subject == subject
            })
            .map(|event| event.sequence)
    }

    pub fn require_event(&self, structure: Structure, action: &str) -> Result<u64, StructureError> {
        self.first_sequence(structure, action).ok_or_else(|| {
            StructureError::new(format!("missing {}.{} event", structure.name(), action))
        })
    }

    pub fn require_event_for(
        &self,
        structure: Structure,
        action: &str,
        subject: &str,
    ) -> Result<u64, StructureError> {
        self.first_sequence_for(structure, action, subject)
            .ok_or_else(|| {
                StructureError::new(format!(
                    "missing {}.{} event for {subject}",
                    structure.name(),
                    action
                ))
            })
    }

    pub fn require_single_event_for(
        &self,
        structure: Structure,
        action: &str,
        subject: &str,
    ) -> Result<&StructuralEvent, StructureError> {
        let mut matches = self.events.iter().filter(|event| {
            event.structure == structure && event.action == action && event.subject == subject
        });
        let event = matches.next().ok_or_else(|| {
            StructureError::new(format!(
                "missing {}.{} event for {subject}",
                structure.name(),
                action
            ))
        })?;
        if matches.next().is_some() {
            return Err(StructureError::new(format!(
                "multiple {}.{} events for {subject}",
                structure.name(),
                action
            )));
        }
        Ok(event)
    }

    pub fn verify_recipe(
        &self,
        required_structures: &[Structure],
        required_edges: &[RecipeEdge],
    ) -> Result<(), StructureError> {
        let observed = self.structures();
        for structure in required_structures {
            if !observed.contains(structure) {
                return Err(StructureError::new(format!(
                    "missing load-bearing structure {}",
                    structure.name()
                )));
            }
        }
        for edge in required_edges {
            let before = self.require_event(edge.before, edge.before_action)?;
            let after = self.require_event(edge.after, edge.after_action)?;
            if before >= after {
                return Err(StructureError::new(format!(
                    "recipe edge {}.{} -> {}.{} is not ordered",
                    edge.before.name(),
                    edge.before_action,
                    edge.after.name(),
                    edge.after_action
                )));
            }
        }
        Ok(())
    }

    pub fn verify_recipe_for(
        &self,
        subject: &str,
        required_structures: &[Structure],
        required_edges: &[RecipeEdge],
    ) -> Result<(), StructureError> {
        for structure in required_structures {
            if !self
                .events
                .iter()
                .any(|event| event.structure == *structure && event.subject == subject)
            {
                return Err(StructureError::new(format!(
                    "missing load-bearing structure {} for {subject}",
                    structure.name()
                )));
            }
        }
        for edge in required_edges {
            let before = self.require_event_for(edge.before, edge.before_action, subject)?;
            let after = self.require_event_for(edge.after, edge.after_action, subject)?;
            if before >= after {
                return Err(StructureError::new(format!(
                    "recipe edge {}.{} -> {}.{} is not ordered for {subject}",
                    edge.before.name(),
                    edge.before_action,
                    edge.after.name(),
                    edge.after_action
                )));
            }
        }
        Ok(())
    }

    /// Verify one uniquely identified recipe instance.
    ///
    /// Unlike `verify_recipe_for`, every edge endpoint must occur exactly once
    /// for the supplied subject. Repeated processes use a distinct subject for
    /// each logical step and call this method for every step.
    pub fn verify_recipe_instance_for(
        &self,
        subject: &str,
        required_structures: &[Structure],
        required_edges: &[RecipeEdge],
    ) -> Result<(), StructureError> {
        for structure in required_structures {
            if !self
                .events
                .iter()
                .any(|event| event.structure == *structure && event.subject == subject)
            {
                return Err(StructureError::new(format!(
                    "missing load-bearing structure {} for {subject}",
                    structure.name()
                )));
            }
        }
        for edge in required_edges {
            let before = self.require_single_event_for(edge.before, edge.before_action, subject)?;
            let after = self.require_single_event_for(edge.after, edge.after_action, subject)?;
            if before.sequence >= after.sequence {
                return Err(StructureError::new(format!(
                    "recipe edge {}.{} -> {}.{} is not ordered for {subject}",
                    edge.before.name(),
                    edge.before_action,
                    edge.after.name(),
                    edge.after_action
                )));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EDGE: RecipeEdge = RecipeEdge {
        before: Structure::CompetitiveSelection,
        before_action: "Commit",
        after: Structure::ActuationPass,
        after_action: "Commit",
    };

    #[test]
    fn instance_verifier_rejects_duplicate_edge_endpoints() {
        let mut trace = TraceLog::default();
        trace.emit(
            Structure::CompetitiveSelection,
            "Commit",
            "tick-0",
            "winner=0",
        );
        trace.emit(Structure::ActuationPass, "Commit", "tick-0", "resource=0");
        trace.emit(Structure::ActuationPass, "Commit", "tick-0", "resource=1");
        assert!(trace
            .verify_recipe_instance_for(
                "tick-0",
                &[Structure::CompetitiveSelection, Structure::ActuationPass],
                &[EDGE],
            )
            .is_err());
    }

    #[test]
    fn instance_subjects_isolate_repeated_steps() {
        let mut trace = TraceLog::default();
        for subject in ["tick-0", "tick-1"] {
            trace.emit(
                Structure::CompetitiveSelection,
                "Commit",
                subject,
                "winner=0",
            );
            trace.emit(Structure::ActuationPass, "Commit", subject, "resource=0");
            trace
                .verify_recipe_instance_for(
                    subject,
                    &[Structure::CompetitiveSelection, Structure::ActuationPass],
                    &[EDGE],
                )
                .unwrap();
        }
    }

    #[test]
    fn a_later_misordered_instance_is_not_hidden_by_an_earlier_one() {
        let mut trace = TraceLog::default();
        trace.emit(
            Structure::CompetitiveSelection,
            "Commit",
            "tick-0",
            "winner=0",
        );
        trace.emit(Structure::ActuationPass, "Commit", "tick-0", "resource=0");
        trace.emit(Structure::ActuationPass, "Commit", "tick-1", "resource=1");
        trace.emit(
            Structure::CompetitiveSelection,
            "Commit",
            "tick-1",
            "winner=1",
        );
        trace
            .verify_recipe_instance_for(
                "tick-0",
                &[Structure::CompetitiveSelection, Structure::ActuationPass],
                &[EDGE],
            )
            .unwrap();
        assert!(trace
            .verify_recipe_instance_for(
                "tick-1",
                &[Structure::CompetitiveSelection, Structure::ActuationPass],
                &[EDGE],
            )
            .is_err());
    }
}
