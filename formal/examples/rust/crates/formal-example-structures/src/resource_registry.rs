use crate::{Structure, StructureError, TraceLog};
use serde::Serialize;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ResourceRegistry<T> {
    records: BTreeMap<String, T>,
}

impl<T> ResourceRegistry<T> {
    pub fn empty(trace: &mut TraceLog, subject: &str) -> Self {
        trace.emit(
            Structure::ResourceRegistry,
            "Initialize",
            subject,
            "records=0",
        );
        Self {
            records: BTreeMap::new(),
        }
    }

    pub fn build(
        records: impl IntoIterator<Item = (String, T)>,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        let mut registry = BTreeMap::new();
        for (id, record) in records {
            if id.is_empty() {
                return Err(StructureError::new(
                    "resource registry contains an empty ID",
                ));
            }
            if registry.insert(id.clone(), record).is_some() {
                return Err(StructureError::new(format!(
                    "resource registry contains duplicate ID {id}"
                )));
            }
        }
        trace.emit(
            Structure::ResourceRegistry,
            "Commit",
            subject,
            format!("records={}", registry.len()),
        );
        Ok(Self { records: registry })
    }

    pub fn get(&self, id: &str) -> Option<&T> {
        self.records.get(id)
    }

    pub fn insert(
        &mut self,
        id: String,
        record: T,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        if id.is_empty() {
            return Err(StructureError::new(
                "resource registry cannot store an empty ID",
            ));
        }
        if self.records.insert(id.clone(), record).is_some() {
            return Err(StructureError::new(format!(
                "resource registry cannot replace existing ID {id}"
            )));
        }
        trace.emit(
            Structure::ResourceRegistry,
            "Store",
            subject,
            format!("id={id} records={}", self.records.len()),
        );
        Ok(())
    }

    pub fn contains(&self, id: &str) -> bool {
        self.records.contains_key(id)
    }

    pub fn ids(&self) -> impl Iterator<Item = &String> {
        self.records.keys()
    }

    pub fn len(&self) -> usize {
        self.records.len()
    }

    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }
}
