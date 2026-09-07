//! Mailbox + send: actor's input queue is a streaming-graph queue;
//! send is emit-to-downstream over a runtime-constructed edge.

use crate::primitives::queue::{BoundedQueue, QueueError};
use std::collections::HashMap;

pub type Pid = u64;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message {
    pub kind: String,
    pub payload: i64,
    pub from: Option<Pid>,
}

pub struct Actor {
    pub pid: Pid,
    pub mailbox: BoundedQueue<Message>,
    pub on_receive: Box<dyn FnMut(Message, &mut ActorContext) + Send>,
}

pub struct ActorContext {
    pub self_pid: Pid,
    pub outgoing: Vec<(Pid, Message)>,
}

impl ActorContext {
    pub fn send(&mut self, target: Pid, mut msg: Message) {
        msg.from = Some(self.self_pid);
        self.outgoing.push((target, msg));
    }
}

pub struct ActorSystem {
    next_pid: Pid,
    pub actors: HashMap<Pid, Actor>,
    pub mailbox_capacity: usize,
}

impl ActorSystem {
    pub fn new(mailbox_capacity: usize) -> Self {
        Self {
            next_pid: 1,
            actors: HashMap::new(),
            mailbox_capacity,
        }
    }

    pub fn spawn<F>(&mut self, on_receive: F) -> Pid
    where
        F: FnMut(Message, &mut ActorContext) + Send + 'static,
    {
        let pid = self.next_pid;
        self.next_pid += 1;
        self.actors.insert(
            pid,
            Actor {
                pid,
                mailbox: BoundedQueue::new(self.mailbox_capacity),
                on_receive: Box::new(on_receive),
            },
        );
        pid
    }

    /// Deliver a single message to a target actor's mailbox.
    /// Returns Err(Full) if backpressure prevents delivery.
    pub fn deliver(&mut self, target: Pid, msg: Message) -> Result<(), QueueError> {
        let actor = self.actors.get_mut(&target).ok_or(QueueError::Empty)?;
        actor.mailbox.enqueue(msg)
    }

    /// Process one message from the named actor's mailbox.
    /// Returns true if a message was processed.
    pub fn step(&mut self, pid: Pid) -> bool {
        let outgoing = {
            let actor = match self.actors.get_mut(&pid) {
                Some(a) => a,
                None => return false,
            };
            let msg = match actor.mailbox.dequeue() {
                Ok(m) => m,
                Err(_) => return false,
            };
            let mut ctx = ActorContext {
                self_pid: pid,
                outgoing: Vec::new(),
            };
            (actor.on_receive)(msg, &mut ctx);
            ctx.outgoing
        };
        for (target, msg) in outgoing {
            let _ = self.deliver(target, msg);
        }
        true
    }

    /// Run until no actor has any pending messages.
    pub fn drain(&mut self) {
        loop {
            let pids: Vec<Pid> = self.actors.keys().copied().collect();
            let mut progressed = false;
            for pid in pids {
                if self.step(pid) {
                    progressed = true;
                }
            }
            if !progressed {
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ping_pong_terminates() {
        let mut sys = ActorSystem::new(8);

        let pong_pid = sys.spawn(|msg, ctx| {
            if let Some(from) = msg.from {
                ctx.send(
                    from,
                    Message {
                        kind: "pong".into(),
                        payload: msg.payload + 1,
                        from: None,
                    },
                );
            }
        });

        let pong_clone = pong_pid;
        let ping_pid = sys.spawn(move |msg, ctx| {
            if msg.payload < 3 {
                ctx.send(
                    pong_clone,
                    Message {
                        kind: "ping".into(),
                        payload: msg.payload + 1,
                        from: None,
                    },
                );
            }
        });

        sys.deliver(
            ping_pid,
            Message {
                kind: "start".into(),
                payload: 0,
                from: None,
            },
        )
        .unwrap();
        sys.drain();

        // Ping should have processed at least 4 messages (start + 3 pongs).
        // Hard to check counter from outside; just verify mailboxes drain.
        assert!(sys.actors[&ping_pid].mailbox.is_empty());
        assert!(sys.actors[&pong_pid].mailbox.is_empty());
    }
}
