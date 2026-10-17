use crate::{Structure, StructureError, TraceLog};
use automation_structures::connectives::ordering_pass::{IndexArrangement, PositionOrder};
use automation_structures::primitives::quality_hierarchy::QualityHierarchy as CanonicalHierarchy;
use automation_structures::primitives::resource_registry::{
    ByteKey, IndexedStorage, ResourceRegistry as CanonicalRegistry,
};
use serde::ser::{SerializeMap, SerializeStruct};
use serde::{Serialize, Serializer};
use std::fmt::{Debug, Formatter};
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct QualityNode {
    pub id: String,
    pub parent: Option<String>,
    pub level: u32,
    pub cost: u64,
}

#[derive(Clone)]
pub struct QualityHierarchy {
    binding: Arc<HierarchyBinding>,
}

struct HierarchyBinding {
    owner: CanonicalHierarchy,
    ids: CanonicalRegistry<ByteKey, usize, IndexedStorage>,
    order: IndexArrangement,
    nodes: Vec<QualityNode>,
}

// Pure String comparison; the published arrangement owns ordering.
struct NodeOrder<'a>(&'a [QualityNode]);
impl PositionOrder for NodeOrder<'_> {
    fn len(&self) -> usize {
        self.0.len()
    }
    fn compare(&self, left: usize, right: usize) -> i8 {
        match self
            .0
            .get(left)
            .map(|node| &node.id)
            .cmp(&self.0.get(right).map(|node| &node.id))
        {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        }
    }
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
        let mut ids = CanonicalRegistry::new_indexed();
        let mut owner = CanonicalHierarchy::try_new(nodes.len(), u64::MAX)
            .map_err(|_| StructureError::new("quality hierarchy storage refused"))?;
        let order = IndexArrangement::try_new(nodes.len(), &NodeOrder(&nodes))
            .map_err(|_| StructureError::new("quality hierarchy order storage refused"))?;
        for (position, node) in nodes.iter().enumerate() {
            let mut key = Vec::new();
            key.try_reserve_exact(node.id.len())
                .map_err(|_| StructureError::new("quality hierarchy key storage refused"))?;
            key.extend_from_slice(node.id.as_bytes());
            ids.try_insert_unique(ByteKey::from_bytes(key), position)
                .map_err(|(reason, _, _)| {
                    StructureError::new(format!("quality hierarchy unique ID refused: {reason:?}"))
                })?;
            if !owner.can_set_node_properties(position, u64::from(node.level), node.cost) {
                return Err(StructureError::new("quality hierarchy properties refused"));
            }
            owner.set_node_properties(position, u64::from(node.level), node.cost);
        }
        for (child, node) in nodes.iter().enumerate() {
            if let Some(parent_id) = &node.parent {
                let parent = ids
                    .lookup_query(&parent_id.as_bytes())
                    .copied()
                    .ok_or_else(|| {
                        StructureError::new(format!("missing quality parent {parent_id}"))
                    })?;
                if !owner.can_add_child(parent, child) {
                    let message = if parent == child {
                        "quality hierarchy contains a self edge".to_owned()
                    } else if owner.level_of(parent) <= owner.level_of(child) {
                        format!(
                            "quality edge {parent_id} -> {} does not strictly descend",
                            node.id
                        )
                    } else if owner.cost_of(parent) > owner.cost_of(child) {
                        format!("quality edge {parent_id} -> {} decreases cost", node.id)
                    } else {
                        format!("quality edge {parent_id} -> {} refused", node.id)
                    };
                    return Err(StructureError::new(message));
                }
                owner.add_child(parent, child);
            }
        }
        trace.emit(
            Structure::QualityHierarchy,
            "Commit",
            subject,
            format!("nodes={} edges={}", owner.num_nodes, owner.edges.len()),
        );
        Ok(Self {
            binding: Arc::new(HierarchyBinding {
                owner,
                ids,
                order,
                nodes,
            }),
        })
    }

    pub fn node(&self, id: &str) -> Option<&QualityNode> {
        let position = self.binding.ids.lookup_query(&id.as_bytes())?;
        self.binding.nodes.get(*position)
    }

    fn ordered_nodes(&self) -> impl Iterator<Item = (usize, &QualityNode)> {
        self.binding
            .order
            .positions()
            .iter()
            .filter_map(|position| {
                self.binding
                    .nodes
                    .get(*position)
                    .map(|node| (*position, node))
            })
    }

    pub fn roots(&self) -> Vec<String> {
        self.ordered_nodes()
            .filter(|(position, _)| {
                self.binding.owner.parent_of(*position) == self.binding.owner.num_nodes
            })
            .map(|(_, node)| node.id.clone())
            .collect()
    }

    pub fn children(&self, parent: &str) -> Vec<String> {
        let Some(parent) = self.binding.ids.lookup_query(&parent.as_bytes()).copied() else {
            return Vec::new();
        };
        self.ordered_nodes()
            .filter(|(position, _)| self.binding.owner.parent_of(*position) == parent)
            .map(|(_, node)| node.id.clone())
            .collect()
    }

    pub fn len(&self) -> usize {
        self.binding.owner.num_nodes
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

struct NodeView<'a>(&'a QualityHierarchy);
impl Debug for NodeView<'_> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_map()
            .entries(self.0.ordered_nodes().map(|(_, node)| (&node.id, node)))
            .finish()
    }
}
impl Debug for QualityHierarchy {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("QualityHierarchy")
            .field("nodes", &NodeView(self))
            .finish()
    }
}
impl PartialEq for QualityHierarchy {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self
                .ordered_nodes()
                .all(|(_, node)| other.node(&node.id) == Some(node))
    }
}
impl Eq for QualityHierarchy {}
impl Serialize for NodeView<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.0.len()))?;
        for (_, node) in self.0.ordered_nodes() {
            map.serialize_entry(&node.id, node)?;
        }
        map.end()
    }
}
impl Serialize for QualityHierarchy {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut structure = serializer.serialize_struct("QualityHierarchy", 1)?;
        structure.serialize_field("nodes", &NodeView(self))?;
        structure.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(id: &str, parent: Option<&str>, level: u32, cost: u64) -> QualityNode {
        QualityNode {
            id: id.into(),
            parent: parent.map(str::to_owned),
            level,
            cost,
        }
    }

    #[test]
    fn lexical_observations_and_content_match_actual_owner() -> Result<(), StructureError> {
        let mut trace = TraceLog::default();
        let hierarchy = QualityHierarchy::build(
            vec![
                node("z", Some("r"), 0, u64::MAX),
                node("r", None, 1, u64::MAX),
                node("a", Some("r"), 0, u64::MAX),
                node("", None, 0, 0),
            ],
            &mut trace,
            "forest",
        )?;
        assert_eq!(hierarchy.roots(), vec!["", "r"]);
        assert_eq!(hierarchy.children("r"), vec!["a", "z"]);
        assert!(hierarchy.children("missing").is_empty());
        for (position, content) in hierarchy.ordered_nodes() {
            assert_eq!(
                hierarchy.binding.owner.level_of(position),
                u64::from(content.level)
            );
            assert_eq!(hierarchy.binding.owner.cost_of(position), content.cost);
            let parent = if let Some(id) = &content.parent {
                hierarchy
                    .binding
                    .ids
                    .lookup_query(&id.as_bytes())
                    .copied()
                    .ok_or_else(|| StructureError::new("parent binding missing"))?
            } else {
                hierarchy.len()
            };
            assert_eq!(hierarchy.binding.owner.parent_of(position), parent);
        }
        assert!(Arc::ptr_eq(&hierarchy.binding, &hierarchy.clone().binding));
        let json = serde_json::to_value(&hierarchy)
            .map_err(|error| StructureError::new(error.to_string()))?;
        assert_eq!(json["nodes"]["z"]["cost"], u64::MAX);
        let text = serde_json::to_string(&hierarchy)
            .map_err(|error| StructureError::new(error.to_string()))?;
        assert!(text.starts_with("{\"nodes\":{\"\":{\"id\":\"\""));
        Ok(())
    }

    #[test]
    fn malformed_forests_publish_no_commit() -> Result<(), StructureError> {
        let cases = [
            vec![node("a", None, 0, 0), node("a", None, 0, 0)],
            vec![node("a", Some("missing"), 0, 0)],
            vec![node("a", Some("a"), 1, 0)],
            vec![node("r", None, 1, 0), node("c", Some("r"), 1, 1)],
            vec![node("r", None, 1, 2), node("c", Some("r"), 0, 1)],
            vec![node("r", Some("c"), 1, 0), node("c", Some("r"), 0, 0)],
        ];
        for nodes in cases {
            let mut trace = TraceLog::default();
            assert!(QualityHierarchy::build(nodes, &mut trace, "refusal").is_err());
            assert!(!trace.events().iter().any(|event| event.action == "Commit"));
        }
        let empty = QualityHierarchy::build(Vec::new(), &mut TraceLog::default(), "empty")?;
        assert!(empty.is_empty());
        assert!(empty.roots().is_empty());
        Ok(())
    }
}
