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

    /// Resolve only the reviewed adapter/action pair. Reduction has no unqualified
    /// identity: a path comparison and an owned fold are different operations.
    pub fn implementation_identity(self, action: Option<&str>) -> Option<&'static str> {
        match (self, action) {
            (
                Self::ActuationPass,
                None
                | Some(
                    "Initialize" | "Allocate" | "Deallocate" | "Attempt" | "Check" | "Commit"
                    | "Finish",
                ),
            ) => Some("formal-example-structures::actuation::ActuationPass"),
            (Self::AllocationSnapshot, None | Some("Commit")) => {
                Some("formal-example-structures::snapshot::AllocationSnapshot")
            }
            (Self::Budget, None | Some("Initialize" | "Check" | "Reject" | "Commit")) => {
                Some("formal-example-structures::budget::Budget")
            }
            (Self::CompetitiveSelection, None | Some("Evaluate" | "Commit")) => {
                Some("formal-example-structures::selection::CompetitiveSelection")
            }
            (
                Self::ForkJoin,
                None
                | Some(
                    "Initialize" | "StartWorker" | "CompleteWorker" | "Barrier" | "ProduceOutput"
                    | "Done",
                ),
            ) => Some("formal-example-structures::fork_join::ForkJoin"),
            (Self::QualityHierarchy, None | Some("Validate" | "Commit")) => {
                Some("formal-example-structures::quality_hierarchy::QualityHierarchy")
            }
            (Self::Reduction, Some("Evaluate" | "Commit")) => {
                Some("formal-example-structures::reduction::Reduction::fold")
            }
            (Self::Reduction, Some("Compare")) => {
                Some("formal-example-structures::reduction::PathReduction::compare")
            }
            (Self::RelationshipGraph, None | Some("Commit")) => {
                Some("formal-example-structures::relationship_graph::RelationshipGraph")
            }
            (Self::ResourceRegistry, None | Some("Initialize" | "Commit" | "Store")) => {
                Some("formal-example-structures::resource_registry::ResourceRegistry")
            }
            (Self::Sequential, None | Some("Initialize" | "Begin" | "Complete" | "Done")) => {
                Some("formal-example-structures::sequential::Sequential")
            }
            (
                Self::StepGraph,
                None
                | Some("Initialize" | "BecomeReady" | "StartRunning" | "CompleteNode" | "Done"),
            ) => Some("formal-example-structures::step_graph::StepGraph"),
            (
                Self::TraversalEngine,
                None | Some("Initialize" | "Enqueue" | "Visit" | "Accept" | "Complete"),
            ) => Some("formal-example-structures::traversal::TraversalEngine"),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct StructuralEvent {
    pub sequence: u64,
    pub structure: Structure,
    pub action: String,
    pub implementation_identity: Option<&'static str>,
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
        let action = action.into();
        let implementation_identity = structure.implementation_identity(Some(&action));
        self.events.push(StructuralEvent {
            sequence,
            structure,
            action,
            implementation_identity,
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
        for event in &self.events {
            if event.implementation_identity.is_none()
                || event.implementation_identity
                    != event.structure.implementation_identity(Some(&event.action))
            {
                return Err(StructureError::new(
                    "unresolved or incorrect trace implementation identity",
                ));
            }
        }
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
        for event in self.events.iter().filter(|event| event.subject == subject) {
            if event.implementation_identity.is_none()
                || event.implementation_identity
                    != event.structure.implementation_identity(Some(&event.action))
            {
                return Err(StructureError::new(
                    "unresolved or incorrect trace implementation identity",
                ));
            }
        }
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
        for event in self.events.iter().filter(|event| event.subject == subject) {
            if event.implementation_identity.is_none()
                || event.implementation_identity
                    != event.structure.implementation_identity(Some(&event.action))
            {
                return Err(StructureError::new(
                    "unresolved or incorrect trace implementation identity",
                ));
            }
        }
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

    #[test]
    fn implementation_identities_resolve_compiled_types_and_exact_reduction_actions() {
        for (structure, compiled) in [
            (
                Structure::ActuationPass,
                std::any::type_name::<crate::ActuationPass>(),
            ),
            (
                Structure::AllocationSnapshot,
                std::any::type_name::<crate::AllocationSnapshot<u64>>(),
            ),
            (
                Structure::Budget,
                std::any::type_name::<crate::Budget<crate::Bytes>>(),
            ),
            (
                Structure::CompetitiveSelection,
                std::any::type_name::<crate::CompetitiveSelection>(),
            ),
            (
                Structure::ForkJoin,
                std::any::type_name::<crate::ForkJoin>(),
            ),
            (
                Structure::QualityHierarchy,
                std::any::type_name::<crate::QualityHierarchy>(),
            ),
            (
                Structure::RelationshipGraph,
                std::any::type_name::<crate::RelationshipGraph>(),
            ),
            (
                Structure::ResourceRegistry,
                std::any::type_name::<crate::ResourceRegistry<u64>>(),
            ),
            (
                Structure::Sequential,
                std::any::type_name::<crate::Sequential<u64>>(),
            ),
            (
                Structure::StepGraph,
                std::any::type_name::<crate::StepGraph>(),
            ),
            (
                Structure::TraversalEngine,
                std::any::type_name::<crate::TraversalEngine<u64>>(),
            ),
        ] {
            let expected = compiled
                .split('<')
                .next()
                .expect("compiled type prefix")
                .replacen(
                    "formal_example_structures::",
                    "formal-example-structures::",
                    1,
                );
            assert_eq!(
                structure.implementation_identity(None),
                Some(expected.as_str())
            );
            assert_eq!(
                structure.implementation_identity(Some("NonexistentAction")),
                None
            );
        }
        assert_eq!(Structure::Reduction.implementation_identity(None), None);
        assert_eq!(
            Structure::Reduction.implementation_identity(Some("Apply")),
            None
        );
        let mut fold = TraceLog::default();
        assert_eq!(
            crate::Reduction::fold([1u64, 2], 0, |a, b| a + b, &mut fold, "fold").expect("fold"),
            3
        );
        let fold_identity = format!(
            "{}::fold",
            std::any::type_name::<crate::Reduction>().replacen(
                "formal_example_structures::",
                "formal-example-structures::",
                1
            )
        );
        assert!(fold
            .events()
            .iter()
            .all(|event| event.implementation_identity == Some(fold_identity.as_str())));
        let mut path = TraceLog::default();
        assert_eq!(
            crate::PathReduction::compare(None, 3, &mut path, "path"),
            crate::Relaxation::Install
        );
        let path_identity = format!(
            "{}::compare",
            std::any::type_name::<crate::PathReduction>().replacen(
                "formal_example_structures::",
                "formal-example-structures::",
                1
            )
        );
        assert_eq!(path.events()[0].action, "Compare");
        assert_eq!(
            path.events()[0].implementation_identity,
            Some(path_identity.as_str())
        );
        assert_ne!(fold_identity, path_identity);
    }

    #[test]
    fn trace_rejects_wrong_operation_identity_and_unsupported_action() {
        let mut trace = TraceLog::default();
        crate::Reduction::fold([1u64], 0, |a, b| a + b, &mut trace, "fold").expect("fold");
        trace
            .verify_recipe_for("fold", &[Structure::Reduction], &[])
            .expect("actual fold binding");
        trace.events[0].implementation_identity =
            Structure::Reduction.implementation_identity(Some("Compare"));
        assert!(trace
            .verify_recipe_for("fold", &[Structure::Reduction], &[])
            .is_err());
        trace.events[0].implementation_identity =
            Structure::Reduction.implementation_identity(Some("Evaluate"));
        trace.emit(
            Structure::Reduction,
            "NonexistentAction",
            "fold",
            "same result",
        );
        assert!(trace
            .verify_recipe_for("fold", &[Structure::Reduction], &[])
            .is_err());
        assert!(trace.verify_recipe(&[Structure::Reduction], &[]).is_err());
        assert!(trace
            .verify_recipe_instance_for("fold", &[Structure::Reduction], &[])
            .is_err());
    }

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
