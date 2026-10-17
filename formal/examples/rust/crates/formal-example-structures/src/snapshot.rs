use crate::{Structure, StructureError, TraceLog};
use automation_structures::compositions::allocation_snapshot::{
    AllocationDomain, SealedTypedAllocation, TypedAllocation,
};
use automation_structures::compositions::reduction::IncrementalReduction;
use automation_structures::primitives::audit_sink::AdditiveChain;
use automation_structures::primitives::resource_registry::ByteKey;
use serde::ser::SerializeStruct;
use serde::Serialize;
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct AllocationRecord<T> {
    pub id: String,
    pub cost: u64,
    pub value: T,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SnapshotMode {
    Bounded { capacity: u64, remaining: u64 },
    Committed,
}

struct RecordDomain<T> {
    records: Arc<Vec<AllocationRecord<T>>>,
    bounded: bool,
}

impl<T> AllocationDomain<ByteKey, usize> for RecordDomain<T> {
    fn admits_exec(&self, key: &ByteKey, position: &usize, charges: &Vec<u64>) -> bool {
        self.records.get(*position).is_some_and(|record| {
            key.as_bytes() == record.id.as_bytes()
                && if self.bounded {
                    charges.as_slice() == [1, record.cost]
                } else {
                    charges.is_empty()
                }
        })
    }
}

/// Immutable authored content admitted by the published allocation profile.
/// Clones share the sealed owner; interior mutability in T remains a domain rely.
pub struct AllocationSnapshot<T> {
    allocation: Arc<SealedTypedAllocation<ByteKey, usize, RecordDomain<T>>>,
    records: Arc<Vec<AllocationRecord<T>>>,
    total_cost: u64,
    mode: SnapshotMode,
}

impl<T> AllocationSnapshot<T> {
    pub fn bounded(
        records: Vec<AllocationRecord<T>>,
        capacity: u64,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        Self::capture(records, Some(capacity), trace, subject)
    }

    pub fn committed(
        records: Vec<AllocationRecord<T>>,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        Self::capture(records, None, trace, subject)
    }

    fn capture(
        records: Vec<AllocationRecord<T>>,
        capacity: Option<u64>,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        let records = Arc::new(records);
        let domain = RecordDomain {
            records: Arc::clone(&records),
            bounded: capacity.is_some(),
        };
        let mut allocation = if let Some(capacity) = capacity {
            let count = u64::try_from(records.len())
                .map_err(|_| StructureError::new("snapshot member count overflow"))?;
            let mut dimensions = Vec::new();
            dimensions
                .try_reserve_exact(2)
                .map_err(|_| StructureError::new("snapshot schema storage refused"))?;
            dimensions.extend([count, capacity]);
            TypedAllocation::try_new(&dimensions, domain).map_err(|reason| {
                StructureError::new(format!("snapshot schema refused: {reason:?}"))
            })?
        } else {
            TypedAllocation::unbudgeted(domain)
        };
        let mut cost = capacity
            .is_none()
            .then(|| IncrementalReduction::new(records.len(), AdditiveChain));
        for (position, record) in records.iter().enumerate() {
            let mut key = Vec::new();
            key.try_reserve_exact(record.id.len())
                .map_err(|_| StructureError::new("snapshot key storage refused"))?;
            key.extend_from_slice(record.id.as_bytes());
            let mut charges = Vec::new();
            if capacity.is_some() {
                charges
                    .try_reserve_exact(2)
                    .map_err(|_| StructureError::new("snapshot charge storage refused"))?;
                charges.extend([1, record.cost]);
            }
            let prepared = allocation
                .prepare(ByteKey::from_bytes(key), position, charges)
                .map_err(|refused| {
                    StructureError::new(format!("snapshot admission refused: {:?}", refused.reason))
                })?;
            if let Some(cost) = &mut cost {
                cost.prepare(record.cost)
                    .map_err(|_| StructureError::new("allocation cost overflow"))?
                    .commit();
            }
            prepared.commit();
        }
        if allocation.len() != records.len() {
            return Err(StructureError::new(
                "snapshot admission differs from authored records",
            ));
        }
        let (total_cost, mode) = if let Some(cost) = cost {
            (cost.result(), SnapshotMode::Committed)
        } else {
            let (capacity, spent) = allocation
                .budget(1)
                .ok_or_else(|| StructureError::new("snapshot cost dimension missing"))?;
            let remaining = capacity
                .checked_sub(spent)
                .ok_or_else(|| StructureError::new("snapshot cost charge exceeds capacity"))?;
            (
                spent,
                SnapshotMode::Bounded {
                    capacity,
                    remaining,
                },
            )
        };
        let snapshot = Self {
            allocation: Arc::new(allocation.seal()),
            records,
            total_cost,
            mode,
        };
        let detail = match mode {
            SnapshotMode::Bounded { remaining, .. } => format!(
                "mode=bounded records={} total={total_cost} remaining={remaining}",
                snapshot.len()
            ),
            SnapshotMode::Committed => format!(
                "mode=committed records={} total={total_cost}",
                snapshot.len()
            ),
        };
        trace.emit(Structure::AllocationSnapshot, "Commit", subject, detail);
        Ok(snapshot)
    }

    pub fn len(&self) -> usize {
        self.allocation.len()
    }

    pub fn is_empty(&self) -> bool {
        self.allocation.is_empty()
    }

    pub fn records(&self) -> &[AllocationRecord<T>] {
        &self.records
    }

    pub fn total_cost(&self) -> u64 {
        self.total_cost
    }

    pub fn mode(&self) -> &SnapshotMode {
        &self.mode
    }
}

impl<T> Clone for AllocationSnapshot<T> {
    fn clone(&self) -> Self {
        Self {
            allocation: Arc::clone(&self.allocation),
            records: Arc::clone(&self.records),
            total_cost: self.total_cost,
            mode: self.mode,
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for AllocationSnapshot<T> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("AllocationSnapshot")
            .field("records", &self.records)
            .field("total_cost", &self.total_cost)
            .field("mode", &self.mode)
            .finish()
    }
}

impl<T: PartialEq> PartialEq for AllocationSnapshot<T> {
    fn eq(&self, other: &Self) -> bool {
        self.records == other.records
            && self.total_cost == other.total_cost
            && self.mode == other.mode
    }
}
impl<T: Eq> Eq for AllocationSnapshot<T> {}

impl<T: Serialize> Serialize for AllocationSnapshot<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_struct("AllocationSnapshot", 3)?;
        state.serialize_field("records", self.records())?;
        state.serialize_field("total_cost", &self.total_cost)?;
        state.serialize_field("mode", self.mode())?;
        state.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(id: &str, cost: u64) -> AllocationRecord<u64> {
        AllocationRecord {
            id: id.into(),
            cost,
            value: cost,
        }
    }

    #[test]
    fn zero_cost_order_and_serialization_observe_the_sealed_capture() -> Result<(), StructureError>
    {
        let mut trace = TraceLog::default();
        let snapshot = AllocationSnapshot::bounded(
            vec![record("z", 0), record("a", 3)],
            3,
            &mut trace,
            "bounded",
        )?;
        if snapshot.len() != 2
            || snapshot.total_cost() != 3
            || snapshot.mode()
                != &(SnapshotMode::Bounded {
                    capacity: 3,
                    remaining: 0,
                })
            || snapshot
                .records()
                .iter()
                .map(|record| record.id.as_str())
                .collect::<Vec<_>>()
                != ["z", "a"]
        {
            return Err(StructureError::new("sealed bounded observation differs"));
        }
        for (position, record) in snapshot.records().iter().enumerate() {
            if snapshot.allocation.get_query(&record.id.as_bytes()) != Some(&position) {
                return Err(StructureError::new(
                    "sealed membership lost authored position",
                ));
            }
        }
        let expected = serde_json::json!({
            "records": [{"id":"z","cost":0,"value":0},{"id":"a","cost":3,"value":3}],
            "total_cost":3,"mode":{"kind":"bounded","capacity":3,"remaining":0}
        });
        if serde_json::to_value(&snapshot)
            .map_err(|error| StructureError::new(error.to_string()))?
            != expected
        {
            return Err(StructureError::new("snapshot serialization changed"));
        }
        Ok(())
    }

    #[test]
    fn empty_and_unbudgeted_captures_share_sealed_content_without_payload_clone(
    ) -> Result<(), StructureError> {
        struct Payload;
        let mut trace = TraceLog::default();
        let empty = AllocationSnapshot::<Payload>::bounded(Vec::new(), 0, &mut trace, "empty")?;
        if !empty.is_empty() || empty.total_cost() != 0 {
            return Err(StructureError::new("empty capture differs"));
        }
        let snapshot = AllocationSnapshot::committed(
            vec![AllocationRecord {
                id: "route".into(),
                cost: u64::MAX,
                value: Payload,
            }],
            &mut trace,
            "routing",
        )?;
        let copied = snapshot.clone();
        if copied.total_cost() != u64::MAX
            || copied.mode() != &SnapshotMode::Committed
            || copied.allocation.budget(0).is_some()
            || !Arc::ptr_eq(&snapshot.allocation, &copied.allocation)
            || !Arc::ptr_eq(&snapshot.records, &copied.records)
        {
            return Err(StructureError::new("unbudgeted sealed copy differs"));
        }
        Ok(())
    }

    #[test]
    fn duplicate_capacity_and_cost_overflow_refuse_before_capture_publication(
    ) -> Result<(), StructureError> {
        for (records, capacity) in [
            (vec![record("same", 0), record("same", 1)], None),
            (vec![record("first", 2), record("second", 2)], Some(3)),
            (vec![record("first", u64::MAX), record("second", 1)], None),
        ] {
            let mut trace = TraceLog::default();
            if AllocationSnapshot::capture(records, capacity, &mut trace, "refused").is_ok()
                || !trace.events().is_empty()
            {
                return Err(StructureError::new("refused capture was published"));
            }
        }
        Ok(())
    }
}
