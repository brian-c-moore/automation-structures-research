use crate::{Structure, StructureError, TraceLog};
use automation_structures::RelationshipGraph as PublishedRelationshipGraph;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Edge {
    pub from: String,
    pub to: String,
    pub weight: u64,
}

#[derive(Serialize)]
pub struct RelationshipGraph {
    #[serde(skip)]
    inner: PublishedRelationshipGraph,
    vertices: BTreeSet<String>,
    edges: Vec<Edge>,
    adjacency: BTreeMap<String, Vec<Edge>>,
}

impl RelationshipGraph {
    pub fn build(
        vertices: impl IntoIterator<Item = String>,
        mut edges: Vec<Edge>,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        let vertices: BTreeSet<String> = vertices.into_iter().collect();
        if vertices.is_empty() {
            return Err(StructureError::new("relationship graph has no vertices"));
        }
        let vertex_index: BTreeMap<String, usize> = vertices
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, vertex)| (vertex, index))
            .collect();
        edges.sort();
        let max_weight = edges.iter().map(|edge| edge.weight).max().unwrap_or(0);
        let mut inner = PublishedRelationshipGraph::new(vertices.len(), max_weight);
        let mut pairs = BTreeSet::new();
        let mut adjacency: BTreeMap<String, Vec<Edge>> = vertices
            .iter()
            .map(|vertex| (vertex.clone(), Vec::new()))
            .collect();
        for edge in &edges {
            if edge.from == edge.to {
                return Err(StructureError::new(format!(
                    "relationship graph contains self edge {}",
                    edge.from
                )));
            }
            if !vertices.contains(&edge.from) || !vertices.contains(&edge.to) {
                return Err(StructureError::new(format!(
                    "relationship edge {} -> {} has an unknown endpoint",
                    edge.from, edge.to
                )));
            }
            if !pairs.insert((edge.from.clone(), edge.to.clone())) {
                return Err(StructureError::new(format!(
                    "relationship graph contains duplicate edge {} -> {}",
                    edge.from, edge.to
                )));
            }
            let source = vertex_index[&edge.from];
            let destination = vertex_index[&edge.to];
            match inner.add_edge(source, destination, edge.weight) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(StructureError::new(format!(
                        "published RelationshipGraph rejected duplicate edge {} -> {}",
                        edge.from, edge.to
                    )));
                }
                Err(error) => {
                    return Err(StructureError::new(format!(
                        "published RelationshipGraph rejected edge {} -> {}: {error}",
                        edge.from, edge.to
                    )));
                }
            }
            adjacency
                .get_mut(&edge.from)
                .expect("validated source vertex")
                .push(edge.clone());
        }
        trace.emit(
            Structure::RelationshipGraph,
            "Commit",
            subject,
            format!("vertices={} edges={}", vertices.len(), edges.len()),
        );
        Ok(Self {
            inner,
            vertices,
            edges,
            adjacency,
        })
    }

    pub fn outgoing(&self, vertex: &str) -> &[Edge] {
        self.adjacency.get(vertex).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn contains_vertex(&self, vertex: &str) -> bool {
        self.vertices.contains(vertex)
    }

    pub fn edges(&self) -> &[Edge] {
        &self.edges
    }
}

impl Clone for RelationshipGraph {
    fn clone(&self) -> Self {
        let vertex_index: BTreeMap<&String, usize> = self
            .vertices
            .iter()
            .enumerate()
            .map(|(index, vertex)| (vertex, index))
            .collect();
        let mut inner = PublishedRelationshipGraph::new(
            self.vertices.len(),
            self.edges.iter().map(|edge| edge.weight).max().unwrap_or(0),
        );
        for edge in &self.edges {
            inner
                .add_edge(
                    vertex_index[&edge.from],
                    vertex_index[&edge.to],
                    edge.weight,
                )
                .expect("validated relationship edge");
        }
        Self {
            inner,
            vertices: self.vertices.clone(),
            edges: self.edges.clone(),
            adjacency: self.adjacency.clone(),
        }
    }
}

impl std::fmt::Debug for RelationshipGraph {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("RelationshipGraph")
            .field("vertices", &self.vertices)
            .field("edges", &self.edges)
            .field("published_edge_count", &self.inner.edge_count())
            .finish()
    }
}

impl PartialEq for RelationshipGraph {
    fn eq(&self, other: &Self) -> bool {
        self.vertices == other.vertices && self.edges == other.edges
    }
}

impl Eq for RelationshipGraph {}
