//! Erlang-style `become`: hot-swap the actor's per-record function.
//!
//! Per docs/execution-modalities.md: "Mutable behavior (Erlang `become`, Pony behaviors)
//! is a dependency-axis change: the operator's effective wiring
//! changes, while the execution primitive does not."

use crate::actor::mailbox::{Message, Pid};
use crate::primitives::queue::BoundedQueue;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BehaviorTag {
    Initial,
    Counting,
    Stopped,
}

pub struct BecomeActor {
    pub pid: Pid,
    pub mailbox: BoundedQueue<Message>,
    pub behavior: BehaviorTag,
    pub state: i64,
}

impl BecomeActor {
    pub fn new(pid: Pid, mailbox_capacity: usize) -> Self {
        Self {
            pid,
            mailbox: BoundedQueue::new(mailbox_capacity),
            behavior: BehaviorTag::Initial,
            state: 0,
        }
    }

    /// Step one message. The behavior tag determines the function;
    /// `become` is implemented as a state field swap. The execution
    /// primitive (consume from mailbox, run, emit) is unchanged.
    pub fn step(&mut self) -> Option<Message> {
        let msg = self.mailbox.dequeue().ok()?;
        match self.behavior {
            BehaviorTag::Initial => {
                if msg.kind == "start" {
                    self.behavior = BehaviorTag::Counting;
                    self.state = msg.payload;
                }
                None
            }
            BehaviorTag::Counting => {
                if msg.kind == "tick" {
                    self.state += msg.payload;
                    Some(Message {
                        kind: "count".into(),
                        payload: self.state,
                        from: Some(self.pid),
                    })
                } else if msg.kind == "stop" {
                    self.behavior = BehaviorTag::Stopped;
                    None
                } else {
                    None
                }
            }
            BehaviorTag::Stopped => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn become_swaps_function_without_changing_primitive() {
        let mut actor = BecomeActor::new(1, 8);
        actor
            .mailbox
            .enqueue(Message {
                kind: "start".into(),
                payload: 100,
                from: None,
            })
            .unwrap();
        actor
            .mailbox
            .enqueue(Message {
                kind: "tick".into(),
                payload: 1,
                from: None,
            })
            .unwrap();
        actor
            .mailbox
            .enqueue(Message {
                kind: "tick".into(),
                payload: 2,
                from: None,
            })
            .unwrap();
        actor
            .mailbox
            .enqueue(Message {
                kind: "stop".into(),
                payload: 0,
                from: None,
            })
            .unwrap();
        actor
            .mailbox
            .enqueue(Message {
                kind: "tick".into(),
                payload: 99,
                from: None,
            })
            .unwrap();

        let r1 = actor.step();
        assert_eq!(r1, None);
        assert_eq!(actor.behavior, BehaviorTag::Counting);
        let r2 = actor.step();
        assert_eq!(r2.unwrap().payload, 101);
        let r3 = actor.step();
        assert_eq!(r3.unwrap().payload, 103);
        let r4 = actor.step();
        assert_eq!(r4, None);
        assert_eq!(actor.behavior, BehaviorTag::Stopped);
        let r5 = actor.step();
        assert_eq!(r5, None);
    }
}
