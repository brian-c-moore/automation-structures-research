use crate::{Structure, StructureError, TraceLog};
use serde::Serialize;
use std::collections::BTreeSet;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct AllocationRecord<T> {
    pub id: String,
    pub cost: u64,
    pub value: T,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SnapshotMode {
    Bounded { capacity: u64, remaining: u64 },
    Committed,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct AllocationSnapshot<T> {
    records: Vec<AllocationRecord<T>>,
    total_cost: u64,
    mode: SnapshotMode,
}

impl<T> AllocationSnapshot<T> {
    fn validate_records(records: &[AllocationRecord<T>]) -> Result<u64, StructureError> {
        let mut ids = BTreeSet::new();
        let mut total_cost = 0u64;
        for record in records {
            if !ids.insert(&record.id) {
                return Err(StructureError::new(format!(
                    "allocation snapshot contains duplicate ID {}",
                    record.id
                )));
            }
            total_cost = total_cost
                .checked_add(record.cost)
                .ok_or_else(|| StructureError::new("allocation cost overflow"))?;
        }
        Ok(total_cost)
    }

    pub fn bounded(
        records: Vec<AllocationRecord<T>>,
        capacity: u64,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        let total_cost = Self::validate_records(&records)?;
        if total_cost > capacity {
            return Err(StructureError::new(format!(
                "snapshot cost {total_cost} exceeds capacity {capacity}"
            )));
        }
        let remaining = capacity - total_cost;
        trace.emit(
            Structure::AllocationSnapshot,
            "Commit",
            subject,
            format!(
                "mode=bounded records={} total={total_cost} remaining={remaining}",
                records.len()
            ),
        );
        Ok(Self {
            records,
            total_cost,
            mode: SnapshotMode::Bounded {
                capacity,
                remaining,
            },
        })
    }

    pub fn committed(
        records: Vec<AllocationRecord<T>>,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<Self, StructureError> {
        let total_cost = Self::validate_records(&records)?;
        trace.emit(
            Structure::AllocationSnapshot,
            "Commit",
            subject,
            format!(
                "mode=committed records={} total={total_cost}",
                records.len()
            ),
        );
        Ok(Self {
            records,
            total_cost,
            mode: SnapshotMode::Committed,
        })
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
