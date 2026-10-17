use crate::{Structure, StructureError, TraceLog};
use automation_structures::compositions::reduction::{
    OwnedReductionError, OwnedReductionOperation, VersionedReduction,
};
use serde::Serialize;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub enum Relaxation {
    Install,
    Replace,
    Equal,
    Reject,
}

pub struct PathReduction;

pub struct Reduction;

struct Combine<'a, F> {
    combine: &'a F,
}

// Pure domain policy; the canonical composition retains every version and prefix.
impl<T: Clone, F: Fn(T, T) -> T> OwnedReductionOperation<T> for Combine<'_, F> {
    type View = T;

    fn try_combine(&self, previous: &T, input: &T) -> Result<T, OwnedReductionError> {
        Ok((self.combine)(previous.clone(), input.clone()))
    }
}

impl Reduction {
    pub fn fold<T: Clone>(
        candidates: impl IntoIterator<Item = T>,
        identity: T,
        combine: impl Fn(T, T) -> T,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Result<T, StructureError> {
        let mut values = Vec::new();
        for value in candidates {
            values
                .try_reserve(1)
                .map_err(|_| StructureError::new("reduction input storage refused"))?;
            values.push(value);
        }
        trace.emit(
            Structure::Reduction,
            "Evaluate",
            subject,
            format!("candidates={}", values.len()),
        );
        let mut owner =
            VersionedReduction::try_new(identity, values.len(), Combine { combine: &combine })
                .map_err(|_| StructureError::new("reduction initial version storage refused"))?;
        for value in values {
            owner
                .prepare(value)
                .map_err(|(reason, _)| {
                    StructureError::new(format!("reduction record refused: {reason:?}"))
                })?
                .commit();
        }
        let result = owner
            .version(owner.processed_len())
            .ok_or_else(|| StructureError::new("reduction accepted version is absent"))?
            .clone();
        trace.emit(Structure::Reduction, "Commit", subject, "result=stored");
        Ok(result)
    }
}

impl PathReduction {
    pub fn compare(
        current: Option<u64>,
        candidate: u64,
        trace: &mut TraceLog,
        subject: &str,
    ) -> Relaxation {
        let result = match current {
            None => Relaxation::Install,
            Some(value) if candidate < value => Relaxation::Replace,
            Some(value) if candidate == value => Relaxation::Equal,
            Some(_) => Relaxation::Reject,
        };
        trace.emit(
            Structure::Reduction,
            "Compare",
            subject,
            format!("current={current:?} candidate={candidate} result={result:?}"),
        );
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retains_noncommutative_input_order_and_empty_identity() -> Result<(), StructureError> {
        let mut trace = TraceLog::default();
        let append = |mut left: String, right: String| {
            left.push_str(&right);
            left
        };
        assert_eq!(
            Reduction::fold(
                ["b".to_string(), "a".to_string(), "c".to_string()],
                "start:".to_string(),
                append,
                &mut trace,
                "ordered"
            )?,
            "start:bac"
        );
        assert_eq!(
            Reduction::fold(
                std::iter::empty::<String>(),
                "identity".to_string(),
                append,
                &mut trace,
                "empty"
            )?,
            "identity"
        );
        Ok(())
    }
}
