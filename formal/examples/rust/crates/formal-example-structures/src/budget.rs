use crate::{Structure, StructureError, TraceLog};
use automation_structures::Budget as PublishedBudget;
use serde::ser::SerializeStruct;
use serde::Serialize;
use std::marker::PhantomData;

pub trait Unit: Clone + Copy + std::fmt::Debug + Eq + PartialEq {
    const NAME: &'static str;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct Bytes;

impl Unit for Bytes {
    const NAME: &'static str = "Bytes";
}

pub struct Budget<U: Unit> {
    inner: PublishedBudget,
    unit: PhantomData<U>,
}

impl<U: Unit> Budget<U> {
    pub fn new(capacity: u64, trace: &mut TraceLog, subject: &str) -> Self {
        trace.emit(
            Structure::Budget,
            "Initialize",
            subject,
            format!("unit={} capacity={capacity}", U::NAME),
        );
        Self {
            inner: PublishedBudget::new(capacity),
            unit: PhantomData,
        }
    }

    pub fn capacity(&self) -> u64 {
        self.inner.capacity()
    }

    pub fn remaining(&self) -> u64 {
        self.inner.available()
    }

    pub fn spent(&self) -> u64 {
        self.inner.allocated()
    }

    pub fn try_reserve(
        &mut self,
        amount: u64,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<(), StructureError> {
        trace.emit(
            Structure::Budget,
            "Check",
            subject,
            format!("amount={amount} remaining={}", self.remaining()),
        );
        if !self.inner.try_allocate(amount) {
            trace.emit(
                Structure::Budget,
                "Reject",
                subject,
                format!("amount={amount} remaining={}", self.remaining()),
            );
            return Err(StructureError::new(format!(
                "reservation {amount} exceeds remaining {} {}",
                self.remaining(),
                U::NAME
            )));
        }
        trace.emit(
            Structure::Budget,
            "Commit",
            subject,
            format!("amount={amount} remaining={}", self.remaining()),
        );
        Ok(())
    }
}

impl<U: Unit> Clone for Budget<U> {
    fn clone(&self) -> Self {
        let mut inner = PublishedBudget::new(self.capacity());
        assert!(inner.try_allocate(self.spent()));
        Self {
            inner,
            unit: PhantomData,
        }
    }
}

impl<U: Unit> std::fmt::Debug for Budget<U> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Budget")
            .field("capacity", &self.capacity())
            .field("remaining", &self.remaining())
            .field("unit", &U::NAME)
            .finish()
    }
}

impl<U: Unit> PartialEq for Budget<U> {
    fn eq(&self, other: &Self) -> bool {
        self.capacity() == other.capacity() && self.spent() == other.spent()
    }
}

impl<U: Unit> Eq for Budget<U> {}

impl<U: Unit> Serialize for Budget<U> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Budget", 2)?;
        state.serialize_field("capacity", &self.capacity())?;
        state.serialize_field("remaining", &self.remaining())?;
        state.end()
    }
}
