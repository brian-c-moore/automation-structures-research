use crate::{Structure, StructureError, TraceLog};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct QualityNode {
    pub id: String,
    pub parent: Option<String>,
    pub level: u32,
    pub cost: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct QualityHierarchy {
    nodes: BTreeMap<String, QualityNode>,
}

impl QualityHierarchy {
    pub fn build(
        nodes: Vec<QualityNode>,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        trace.emit(
            Structure::QualityHierarchy,
            "Validate",
            subject,
            format!("nodes={}", nodes.len()),
        );
        let mut by_id = BTreeMap::new();
        for node in nodes {
            if by_id.insert(node.id.clone(), node).is_some() {
                return Err(StructureError::new(
                    "quality hierarchy contains a duplicate ID",
                ));
            }
        }
        let mut children = BTreeSet::new();
        for node in by_id.values() {
            if let Some(parent_id) = &node.parent {
                let parent = by_id.get(parent_id).ok_or_else(|| {
                    StructureError::new(format!("missing quality parent {parent_id}"))
                })?;
                if parent.id == node.id {
                    return Err(StructureError::new(
                        "quality hierarchy contains a self edge",
                    ));
                }
                if parent.level <= node.level {
                    return Err(StructureError::new(format!(
                        "quality edge {} -> {} does not strictly descend",
                        parent.id, node.id
                    )));
                }
                if parent.cost > node.cost {
                    return Err(StructureError::new(format!(
                        "quality edge {} -> {} decreases cost",
                        parent.id, node.id
                    )));
                }
                if !children.insert(node.id.clone()) {
                    return Err(StructureError::new(format!(
                        "quality node {} has more than one parent",
                        node.id
                    )));
                }
            }
        }
        trace.emit(
            Structure::QualityHierarchy,
            "Commit",
            subject,
            format!("nodes={} edges={}", by_id.len(), children.len()),
        );
        Ok(Self { nodes: by_id })
    }

    pub fn node(&self, id: &str) -> Option<&QualityNode> {
        self.nodes.get(id)
    }

    pub fn roots(&self) -> Vec<String> {
        self.nodes
            .values()
            .filter(|node| node.parent.is_none())
            .map(|node| node.id.clone())
            .collect()
    }

    pub fn children(&self, parent: &str) -> Vec<String> {
        self.nodes
            .values()
            .filter(|node| node.parent.as_deref() == Some(parent))
            .map(|node| node.id.clone())
            .collect()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}
