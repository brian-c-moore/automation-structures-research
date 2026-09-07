//! Actor pattern equivalence (the execution-modality study).
//!
//! Each actor pattern (mailbox/send, become, selective receive,
//! supervision) is a configuration over the streaming-graph
//! primitives and is verified to behave as documented.

use execution_modalities::actor::become_::{BecomeActor, BehaviorTag};
use execution_modalities::actor::mailbox::{ActorSystem, Message};
use execution_modalities::actor::selective_receive::{KindPattern, SelectiveReceiveActor};
use execution_modalities::actor::supervision::{RestartStrategy, Supervisor};

#[test]
fn mailbox_send_routes_via_runtime_topology() {
    let mut sys = ActorSystem::new(8);
    let echo_pid = sys.spawn(|msg, ctx| {
        if let Some(from) = msg.from {
            ctx.send(
                from,
                Message {
                    kind: "echo".into(),
                    payload: msg.payload,
                    from: None,
                },
            );
        }
    });
    let probe_pid = sys.spawn(|_, _| {});
    sys.deliver(
        echo_pid,
        Message {
            kind: "ping".into(),
            payload: 42,
            from: Some(probe_pid),
        },
    )
    .unwrap();
    sys.drain();
    let inbox = &sys.actors[&probe_pid].mailbox;
    assert!(inbox.is_empty());
}

#[test]
fn become_swaps_function_under_running_primitive() {
    let mut a = BecomeActor::new(1, 4);
    a.mailbox
        .enqueue(Message {
            kind: "start".into(),
            payload: 0,
            from: None,
        })
        .unwrap();
    a.mailbox
        .enqueue(Message {
            kind: "tick".into(),
            payload: 5,
            from: None,
        })
        .unwrap();
    a.step();
    assert_eq!(a.behavior, BehaviorTag::Counting);
    let r = a.step();
    assert_eq!(r.unwrap().payload, 5);
}

#[test]
fn selective_receive_is_invocation_policy_change_only() {
    let mut a = SelectiveReceiveActor::new(1, 8);
    for i in 0..5 {
        let kind = if i % 2 == 0 { "noise" } else { "data" };
        a.mailbox
            .enqueue(Message {
                kind: kind.into(),
                payload: i,
                from: None,
            })
            .unwrap();
    }
    let m = a.receive_matching(&KindPattern("data".into())).unwrap();
    assert_eq!(m.payload, 1);
}

#[test]
fn supervision_restarts_crashed_child() {
    let mut sup = Supervisor::new(RestartStrategy::OneForOne, 2);
    sup.supervise(1);
    sup.child_crashed(1);
    assert!(sup.alive(1));
}
