//! Selective receive (Erlang-style): an invocation policy applied to
//! the mailbox. The actor scans for messages matching a pattern; if
//! none match, the actor blocks until one arrives.
//!
//! Per docs/execution-modalities.md: "Selective receive is an invocation policy: the
//! queue consumption strategy is pattern-match rather than FIFO."

use crate::actor::mailbox::{Message, Pid};
use crate::primitives::queue::BoundedQueue;
use std::collections::VecDeque;

pub trait MessagePattern: Send + Sync {
    fn matches(&self, msg: &Message) -> bool;
}

pub struct KindPattern(pub String);
impl MessagePattern for KindPattern {
    fn matches(&self, msg: &Message) -> bool {
        msg.kind == self.0
    }
}

pub struct SelectiveReceiveActor {
    pub pid: Pid,
    pub mailbox: BoundedQueue<Message>,
}

impl SelectiveReceiveActor {
    pub fn new(pid: Pid, mailbox_capacity: usize) -> Self {
        Self {
            pid,
            mailbox: BoundedQueue::new(mailbox_capacity),
        }
    }

    /// Scan the mailbox for the first message matching `pattern`.
    /// If found, returns that message; the rest of the mailbox is
    /// left in original FIFO order.
    pub fn receive_matching<P: MessagePattern>(&mut self, pattern: &P) -> Option<Message> {
        let mut buffer: VecDeque<Message> = VecDeque::new();
        let mut chosen: Option<Message> = None;

        while let Ok(m) = self.mailbox.dequeue() {
            if chosen.is_none() && pattern.matches(&m) {
                chosen = Some(m);
            } else {
                buffer.push_back(m);
            }
        }

        // Reinsert the unmatched messages, preserving order.
        for m in buffer {
            // Re-enqueue. Capacity is the same, so this cannot fail: at least
            // the same number of messages was just dequeued.
            self.mailbox
                .enqueue(m)
                .expect("mailbox over capacity after selective receive");
        }

        chosen
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selective_receive_finds_kind_match_and_preserves_order() {
        let mut actor = SelectiveReceiveActor::new(1, 8);
        actor
            .mailbox
            .enqueue(Message {
                kind: "noise".into(),
                payload: 1,
                from: None,
            })
            .unwrap();
        actor
            .mailbox
            .enqueue(Message {
                kind: "data".into(),
                payload: 2,
                from: None,
            })
            .unwrap();
        actor
            .mailbox
            .enqueue(Message {
                kind: "noise".into(),
                payload: 3,
                from: None,
            })
            .unwrap();

        let pattern = KindPattern("data".into());
        let m = actor.receive_matching(&pattern).unwrap();
        assert_eq!(m.payload, 2);

        // After receive, the two "noise" messages remain in original order.
        let m1 = actor.mailbox.dequeue().unwrap();
        assert_eq!(m1.payload, 1);
        let m2 = actor.mailbox.dequeue().unwrap();
        assert_eq!(m2.payload, 3);
    }
}
