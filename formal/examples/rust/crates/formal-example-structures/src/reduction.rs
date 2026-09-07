use crate::{Structure, TraceLog};
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

impl Reduction {
    pub fn fold<T>(
        candidates: impl IntoIterator<Item = T>,
        identity: T,
        combine: impl Fn(T, T) -> T,
        trace: &mut TraceLog,
        subject: &str,
    ) -> T {
        let values: Vec<T> = candidates.into_iter().collect();
        trace.emit(
            Structure::Reduction,
            "Evaluate",
            subject,
            format!("candidates={}", values.len()),
        );
        let result = values.into_iter().fold(identity, combine);
        trace.emit(Structure::Reduction, "Commit", subject, "result=stored");
        result
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
            "Commit",
            subject,
            format!("current={current:?} candidate={candidate} result={result:?}"),
        );
        result
    }
}
