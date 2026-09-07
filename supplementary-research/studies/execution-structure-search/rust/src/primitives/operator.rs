//! Operator state machine.
//!
//! Maps to TLA+ `OperatorStates.tla`. An operator is a unit of work
//! whose state machine differs by modality:
//!
//! - completion-bounded modalities (Sequential, ForkJoin, StepGraph)
//!   use NotReady -> Ready -> Running -> Completed
//! - streaming modalities (StreamGraph) use Idle <-> Processing
//!
//! The function transformation an operator performs is opaque to the
//! substrate (`OperatorFn<I, O>` is a boxed closure).

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OperatorState {
    NotReady,
    Ready,
    Running,
    Completed,
    Idle,
    Processing,
}

impl OperatorState {
    pub fn rank(&self) -> i32 {
        match self {
            OperatorState::NotReady => 0,
            OperatorState::Ready => 1,
            OperatorState::Running => 2,
            OperatorState::Completed => 3,
            OperatorState::Idle => 0,
            OperatorState::Processing => 1,
        }
    }
}

pub type OperatorFn<I, O> = Box<dyn Fn(I) -> O + Send + Sync>;

pub struct Operator<I, O> {
    pub id: String,
    pub state: OperatorState,
    pub func: OperatorFn<I, O>,
}

impl<I, O> Operator<I, O> {
    pub fn new(id: impl Into<String>, func: OperatorFn<I, O>) -> Self {
        Self {
            id: id.into(),
            state: OperatorState::NotReady,
            func,
        }
    }

    pub fn apply(&self, input: I) -> O {
        (self.func)(input)
    }

    pub fn transition(&mut self, target: OperatorState) {
        debug_assert!(
            target.rank() >= self.state.rank()
                || (matches!(self.state, OperatorState::Processing)
                    && matches!(target, OperatorState::Idle)),
            "operator state regression: {:?} -> {:?}",
            self.state,
            target
        );
        self.state = target;
    }
}

impl<I, O> std::fmt::Debug for Operator<I, O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Operator")
            .field("id", &self.id)
            .field("state", &self.state)
            .finish()
    }
}
