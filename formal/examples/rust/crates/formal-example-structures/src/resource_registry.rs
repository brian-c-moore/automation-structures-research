use crate::{Structure, StructureError, TraceLog};
use automation_structures::connectives::ordering_pass::{IndexArrangement, PositionOrder};
use automation_structures::primitives::resource_registry::{
    ByteKey, IndexedEntries, IndexedStorage, RegistryPredicate, RegistryStorage,
    ResourceRegistry as CanonicalRegistry,
};
use serde::ser::{SerializeMap, SerializeStruct};
use serde::{Serialize, Serializer};
use std::fmt::{Debug, Formatter};

pub struct ResourceRegistry<T> {
    records: CanonicalRegistry<ByteKey, (String, T), IndexedStorage>,
    order: Option<IndexArrangement>,
}

/// Original content retained when a unique insertion is refused.
pub struct RegistryRefusal<T> {
    pub error: StructureError,
    pub id: String,
    pub record: T,
}

impl<T> From<RegistryRefusal<T>> for StructureError {
    fn from(refused: RegistryRefusal<T>) -> Self {
        refused.error
    }
}

impl<T> Debug for RegistryRefusal<T> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("RegistryRefusal")
            .field("error", &self.error)
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

// Domain comparison only. The published arrangement owns every ordering step.
struct IdOrder<'a, T> {
    entries: &'a IndexedEntries<(String, T)>,
    candidate: &'a str,
    count: usize,
}

impl<T> IdOrder<'_, T> {
    fn id(&self, position: usize) -> Option<&str> {
        if position == self.entries.len() {
            Some(self.candidate)
        } else {
            self.entries.value_at(position).map(|(id, _)| id.as_str())
        }
    }
}

impl<T> PositionOrder for IdOrder<'_, T> {
    fn len(&self) -> usize {
        self.count
    }
    fn compare(&self, left: usize, right: usize) -> i8 {
        match self.id(left).cmp(&self.id(right)) {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        }
    }
}

struct EqualRecords<'a, T> {
    other: &'a ResourceRegistry<T>,
}
impl<T: PartialEq> RegistryPredicate<ByteKey, (String, T)> for EqualRecords<'_, T> {
    fn test(&self, key: &ByteKey, record: &(String, T)) -> bool {
        self.other.records.lookup_key_ref(key) == Some(record)
    }
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
            records: CanonicalRegistry::new_indexed(),
            order: None,
        }
    }

    pub fn build(
        records: impl IntoIterator<Item = (String, T)>,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        let mut registry = Self {
            records: CanonicalRegistry::new_indexed(),
            order: None,
        };
        for (id, record) in records {
            registry
                .insert_owned(id, record)
                .map_err(StructureError::from)?;
        }
        trace.emit(
            Structure::ResourceRegistry,
            "Commit",
            subject,
            format!("records={}", registry.len()),
        );
        Ok(registry)
    }

    pub fn get(&self, id: &str) -> Option<&T> {
        self.records
            .lookup_query(&id.as_bytes())
            .map(|(_, record)| record)
    }

    pub fn insert(
        &mut self,
        id: String,
        record: T,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), RegistryRefusal<T>> {
        let receipt_id = id.clone();
        self.insert_owned(id, record)?;
        trace.emit(
            Structure::ResourceRegistry,
            "Store",
            subject,
            format!("id={receipt_id} records={}", self.len()),
        );
        Ok(())
    }

    fn insert_owned(&mut self, id: String, record: T) -> Result<(), RegistryRefusal<T>> {
        let refuse = |error, id, record| RegistryRefusal {
            error: StructureError::new(error),
            id,
            record,
        };
        if id.is_empty() {
            return Err(refuse(
                "resource registry cannot store an empty ID",
                id,
                record,
            ));
        }
        if self.contains(&id) {
            return Err(RegistryRefusal {
                error: StructureError::new(format!(
                    "resource registry cannot replace existing ID {id}"
                )),
                id,
                record,
            });
        }
        let Some(count) = self.len().checked_add(1) else {
            return Err(refuse("resource registry entry count overflow", id, record));
        };
        let order = match IndexArrangement::try_new(
            count,
            &IdOrder {
                entries: &self.records.entries,
                candidate: &id,
                count,
            },
        ) {
            Ok(order) => order,
            Err(_) => {
                return Err(refuse(
                    "resource registry order reservation refused",
                    id,
                    record,
                ))
            }
        };
        let mut bytes = Vec::new();
        if bytes.try_reserve_exact(id.len()).is_err() {
            return Err(refuse(
                "resource registry key reservation refused",
                id,
                record,
            ));
        }
        bytes.extend_from_slice(id.as_bytes());
        if let Err((_reason, _key, (id, record))) = self
            .records
            .try_insert_unique(ByteKey::from_bytes(bytes), (id, record))
        {
            return Err(refuse(
                "resource registry unique insertion refused",
                id,
                record,
            ));
        }
        self.order = Some(order);
        Ok(())
    }

    pub fn contains(&self, id: &str) -> bool {
        self.records.lookup_query(&id.as_bytes()).is_some()
    }

    pub fn ids(&self) -> impl Iterator<Item = &String> {
        self.order
            .iter()
            .flat_map(IndexArrangement::positions)
            .filter_map(|position| self.records.entries.value_at(*position).map(|(id, _)| id))
    }

    pub fn len(&self) -> usize {
        self.records.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Copy domain payloads into a distinct canonical owner; owner-storage refusal is reported.
    /// Payload cloning uses T's own Clone contract and does not promise deep immutability.
    pub fn try_clone(&self) -> Result<Self, StructureError>
    where
        T: Clone,
    {
        let mut copied = Self {
            records: CanonicalRegistry::new_indexed(),
            order: None,
        };
        for id in self.ids() {
            let record = self
                .get(id)
                .ok_or_else(|| StructureError::new("registry projection lost its payload"))?;
            copied
                .insert_owned(id.clone(), record.clone())
                .map_err(StructureError::from)?;
        }
        Ok(copied)
    }
}

struct RecordView<'a, T>(&'a ResourceRegistry<T>);
impl<T: Debug> Debug for RecordView<'_, T> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_map()
            .entries(
                self.0
                    .ids()
                    .filter_map(|id| self.0.get(id).map(|value| (id, value))),
            )
            .finish()
    }
}
impl<T: Debug> Debug for ResourceRegistry<T> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ResourceRegistry")
            .field("records", &RecordView(self))
            .finish()
    }
}
impl<T: PartialEq> PartialEq for ResourceRegistry<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.records.all_matching(&EqualRecords { other })
    }
}
impl<T: Eq> Eq for ResourceRegistry<T> {}
impl<T: Serialize> Serialize for RecordView<'_, T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.0.len()))?;
        for id in self.0.ids() {
            if let Some(value) = self.0.get(id) {
                map.serialize_entry(id, value)?;
            }
        }
        map.end()
    }
}
impl<T: Serialize> Serialize for ResourceRegistry<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut structure = serializer.serialize_struct("ResourceRegistry", 1)?;
        structure.serialize_field("records", &RecordView(self))?;
        structure.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn duplicate_returns_original_payload_and_preserves_mapping_and_order() {
        let mut trace = TraceLog::default();
        let installed = Arc::new(7);
        let duplicate = Arc::new(9);
        let mut registry = ResourceRegistry::empty(&mut trace, "registry");
        assert!(registry
            .insert("z".into(), Arc::clone(&installed), &mut trace, "registry")
            .is_ok());
        assert!(registry
            .insert("a".into(), Arc::new(1), &mut trace, "registry")
            .is_ok());
        let refused = registry
            .insert("z".into(), Arc::clone(&duplicate), &mut trace, "registry")
            .err();
        assert!(refused
            .as_ref()
            .is_some_and(|refused| Arc::ptr_eq(&refused.record, &duplicate)));
        assert!(registry
            .get("z")
            .is_some_and(|value| Arc::ptr_eq(value, &installed)));
        assert_eq!(
            registry.ids().map(String::as_str).collect::<Vec<_>>(),
            vec!["a", "z"]
        );
        assert_eq!(registry.len(), 2);
    }

    #[test]
    fn lexical_serialization_and_empty_id_refusal_preserve_original_schema() {
        let mut trace = TraceLog::default();
        let mut registry = ResourceRegistry::empty(&mut trace, "registry");
        assert!(registry
            .insert("z".into(), 7, &mut trace, "registry")
            .is_ok());
        assert!(registry
            .insert("a".into(), 1, &mut trace, "registry")
            .is_ok());
        assert_eq!(
            serde_json::to_string(&registry).ok().as_deref(),
            Some("{\"records\":{\"a\":1,\"z\":7}}")
        );
        assert!(registry
            .insert(String::new(), 9, &mut trace, "registry")
            .is_err());
        assert_eq!(registry.len(), 2);
    }
}
