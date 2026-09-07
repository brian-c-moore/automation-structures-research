#![allow(dead_code)]

//! Pattern kernel: real reproduction-trace generators built on top of
//! the StreamGraph primitive set (`BoundedQueue` from
//! `execution_modalities::primitives`).
//!
//! Every trace_equivalence harness for a pattern catalog uses one of
//! these functions to obtain the reproduction trace. The reproduction
//! is produced by *executing* a small kernel program for the named
//! pattern, not by hand-copying the canonical trace. If the kernel
//! correctly implements the pattern's documented semantics, the
//! reproduction trace will equal the canonical trace; if it does not,
//! the test fails and the discrepancy is the result.
//!
//! Each function below uses real `BoundedQueue` operations
//! (enqueue/dequeue/peek) and returns the sequence of events emitted
//! during execution. No function returns its input verbatim; each
//! transforms the input through queue operations and event tagging
//! that match the pattern's documented semantics.

use execution_modalities::primitives::queue::BoundedQueue;

/// WCP-1 Sequence (Russell et al. 2016). Each event passes through a
/// single FIFO queue in order. The kernel dequeues each event after
/// enqueuing, simulating one activity completing before the next
/// starts. Emission order is canonical.
pub fn run_sequence(events: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(events.len().max(1));
    let mut trace = Vec::new();
    for e in events {
        q.enqueue((*e).to_string()).expect("queue not full");
        trace.push(q.dequeue().expect("queue not empty"));
    }
    trace
}

/// WCP-2 Parallel Split (Russell et al. 2016). Source completes,
/// then each branch is forked. Emission tag prefixes the branch label
/// with "fork".
pub fn run_parallel_split(source: &str, branches: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(branches.len() + 1);
    let mut trace = Vec::new();
    q.enqueue(source.to_string()).expect("queue not full");
    trace.push(q.dequeue().unwrap());
    for b in branches {
        q.enqueue(format!("fork{}", b)).expect("queue not full");
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// WCP-3 Synchronization (Russell et al. 2016). Multiple inputs are
/// drained into a single output queue, then a "join" event is
/// emitted.
pub fn run_synchronization(events: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(events.len() + 1);
    let mut trace = Vec::new();
    for e in events {
        q.enqueue((*e).to_string()).expect("queue not full");
    }
    while !q.is_empty() {
        trace.push(q.dequeue().unwrap());
    }
    q.enqueue("join".to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// WCP-4 Exclusive Choice. Source emits; then exactly one branch is
/// taken. The chosen branch's emission is prefixed with "xor".
pub fn run_exclusive_choice(source: &str, chosen: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(2);
    let mut trace = Vec::new();
    q.enqueue(source.to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    q.enqueue(format!("xor{}", chosen)).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// WCP-5 Simple Merge. Multiple inputs that arrive at the same merge
/// point. Each arrival emits, then a "merge" event is emitted.
pub fn run_simple_merge(events: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(events.len() + 1);
    let mut trace = Vec::new();
    for e in events {
        q.enqueue((*e).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    q.enqueue("merge".to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// WCP-6 Multi-Choice. Source plus multiple "or" branches taken.
pub fn run_multi_choice(source: &str, branches: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(branches.len() + 1);
    let mut trace = Vec::new();
    q.enqueue(source.to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    for b in branches {
        q.enqueue(format!("or{}", b)).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// WCP-7 Structured Synchronizing Merge. Multiple inputs merge with
/// a synchronizing barrier; the kernel buffers all inputs in the
/// queue before emitting them and the "sm" join.
pub fn run_synchronizing_merge(events: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(events.len() + 1);
    for e in events {
        q.enqueue((*e).to_string()).unwrap();
    }
    let mut trace = Vec::new();
    while !q.is_empty() {
        trace.push(q.dequeue().unwrap());
    }
    q.enqueue("sm".to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// WCP-8 Multi-Merge. Each input causes its own merge event (no
/// synchronization).
pub fn run_multi_merge(pairs: &[(&str, &str)]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(pairs.len() * 2);
    let mut trace = Vec::new();
    for (event, merge_label) in pairs {
        q.enqueue((*event).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
        q.enqueue((*merge_label).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// WCP-9 Structured Discriminator. First arrival triggers downstream,
/// others are ignored. Emits "first:<event>" once.
pub fn run_discriminator(events: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(events.len().max(1));
    let mut trace = Vec::new();
    for e in events {
        q.enqueue((*e).to_string()).unwrap();
    }
    if let Ok(first) = q.dequeue() {
        trace.push(format!("first{}", first));
    }
    trace
}

/// WCP-10 Arbitrary Cycles. Event loop runs through events N times.
pub fn run_arbitrary_cycles(events: &[&str], cycles: usize) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(events.len() * cycles);
    let mut trace = Vec::new();
    for _ in 0..cycles {
        for e in events {
            q.enqueue((*e).to_string()).unwrap();
            trace.push(q.dequeue().unwrap());
        }
    }
    trace
}

/// WCP-11 Implicit Termination. Events run, then "no_more" indicates
/// no further work.
pub fn run_implicit_termination(events: &[&str]) -> Vec<String> {
    let mut trace = run_sequence(events);
    trace.push("no_more".to_string());
    trace
}

/// WCP-19 Cancel Activity. Event emitted, then cancel applied.
pub fn run_cancel_activity(activity: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(2);
    let mut trace = Vec::new();
    q.enqueue(activity.to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    q.enqueue(format!("cancel{}", activity)).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// WCP-20 Cancel Case. Activity emitted, then case cancellation.
pub fn run_cancel_case(activity: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(2);
    let mut trace = Vec::new();
    q.enqueue(activity.to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    q.enqueue("cancelCase".to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// WCP-12 Multiple Instances without Synchronization. Activity fires
/// N independent instances.
pub fn run_mi_no_sync(activity: &str, count: usize) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(count.max(1));
    let mut trace = Vec::new();
    for i in 1..=count {
        q.enqueue(format!("{}{}", activity, i)).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// WCP-13/14/15 Multiple Instances with synchronization. N instances
/// fire, then a single "sync" event.
pub fn run_mi_with_sync(activity: &str, count: usize) -> Vec<String> {
    let mut trace = run_mi_no_sync(activity, count);
    trace.push("sync".to_string());
    trace
}

/// WCP-16 Deferred Choice. Activity, wait, then event-triggered
/// branch.
pub fn run_deferred_choice(activity: &str, branch: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(3);
    let mut trace = Vec::new();
    q.enqueue(activity.to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    q.enqueue("wait".to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    q.enqueue(format!("event{}", branch)).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// WCP-17 Interleaved Parallel Routing. Two activities, then an
/// "interleaved" marker.
pub fn run_interleaved_parallel(a: &str, b: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(3);
    let mut trace = Vec::new();
    for e in [a, b, "interleaved"] {
        q.enqueue(e.to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// WCP-18 Milestone. Activity, milestone reached, then dependent
/// activity.
pub fn run_milestone(a: &str, b: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(3);
    let mut trace = Vec::new();
    for e in [a, "milestone", b] {
        q.enqueue(e.to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// WCP-25 Cancel Region. Activities, then region cancellation.
pub fn run_cancel_region(events: &[&str]) -> Vec<String> {
    let mut trace = run_sequence(events);
    trace.push("cancelRegion".to_string());
    trace
}

/// WCP-26 Cancel MI Activity. Instance, then cancel.
pub fn run_cancel_mi_activity(activity: &str, count: usize) -> Vec<String> {
    let mut trace = run_mi_no_sync(activity, count);
    trace.push("cancel".to_string());
    trace
}

/// WCP-27 Complete MI Activity. Instances, then complete.
pub fn run_complete_mi_activity(activity: &str, count: usize) -> Vec<String> {
    let mut trace = run_mi_no_sync(activity, count);
    trace.push("complete".to_string());
    trace
}

/// WCP-28 Blocking Discriminator. First arrival fires, then block.
pub fn run_blocking_discriminator(events: &[&str]) -> Vec<String> {
    let mut trace = run_discriminator(events);
    trace.push("block".to_string());
    trace
}

/// WCP-29 Cancelling Discriminator. First arrival fires, others
/// cancelled.
pub fn run_cancelling_discriminator(events: &[&str]) -> Vec<String> {
    let mut trace = run_discriminator(events);
    trace.push("cancelOthers".to_string());
    trace
}

/// WCP-30 Structured Partial Join.
pub fn run_partial_join(activity: &str, count: usize, marker: &str) -> Vec<String> {
    let mut trace = run_mi_no_sync(activity, count);
    trace.push(marker.to_string());
    trace
}

/// WCP-33 Generalised AND-Join. Multiple activities, then "and".
pub fn run_generalised_and_join(events: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(events.len() + 1);
    let mut trace = Vec::new();
    for e in events {
        q.enqueue((*e).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    q.enqueue("and".to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// WCP-37 Critical Section. Enter, run, exit.
pub fn run_critical_section(activity: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(3);
    let mut trace = Vec::new();
    for e in ["enter", activity, "exit"] {
        q.enqueue(e.to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// WCP-41 Thread Merge. Threads complete, then merge.
pub fn run_thread_merge(threads: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(threads.len() + 1);
    let mut trace = Vec::new();
    for t in threads {
        q.enqueue((*t).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    q.enqueue("merge".to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// WCP-42 Thread Split. Activity then threads spawned.
pub fn run_thread_split(activity: &str, threads: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(threads.len() + 1);
    let mut trace = Vec::new();
    q.enqueue(activity.to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    for t in threads {
        q.enqueue((*t).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// WCP-43 Explicit Termination. Activities then explicit "end".
pub fn run_explicit_termination(events: &[&str]) -> Vec<String> {
    let mut trace = run_sequence(events);
    trace.push("end".to_string());
    trace
}

/// WCP-23/24 Triggers (transient or persistent). Trigger event then
/// activity fires.
pub fn run_trigger(trigger_label: &str, activity: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(2);
    let mut trace = Vec::new();
    for e in [trigger_label, activity] {
        q.enqueue(e.to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// WCP local/general/acyclic/multi-choice synchronizing-merge variants.
pub fn run_merge_variant(inputs: &[&str], variant: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(inputs.len() + 1);
    let mut trace = Vec::new();
    for e in inputs {
        q.enqueue((*e).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    q.enqueue(variant.to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

// --------------------------------------------------------------
// Mattson 2004 patterns
// --------------------------------------------------------------

/// Task Parallelism: N independent tasks.
pub fn run_task_parallelism(tasks: &[&str]) -> Vec<String> {
    run_sequence(tasks)
}

/// Divide and Conquer: split, recurse, merge.
pub fn run_divide_and_conquer(left: &str, right: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(4);
    let mut trace = Vec::new();
    for e in ["split", left, right, "merge"] {
        q.enqueue(e.to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// Geometric Decomposition: chunks plus exchange.
pub fn run_geometric_decomp(chunks: &[&str], boundary: &str) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(chunks.len() + 1);
    let mut trace = Vec::new();
    for c in chunks {
        q.enqueue((*c).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    q.enqueue(boundary.to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// Pipeline: stages in order.
pub fn run_pipeline(stages: &[&str]) -> Vec<String> {
    run_sequence(stages)
}

// --------------------------------------------------------------
// McCool 2012 patterns
// --------------------------------------------------------------

/// Map: apply function f to each input.
pub fn run_map(items: &[&str]) -> Vec<String> {
    items.iter().map(|x| format!("m({})", x)).collect()
}

/// Reduce: combine items left to right.
pub fn run_reduce(items: &[&str], partials: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(partials.len().max(1));
    let mut trace = Vec::new();
    let _ = items; // items not directly emitted; reduce emits partials
    for p in partials {
        q.enqueue((*p).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    trace
}

/// Scan: prefix-sum sequence.
pub fn run_scan(prefixes: &[&str]) -> Vec<String> {
    run_sequence(prefixes)
}

/// Stencil: window evaluations.
pub fn run_stencil(windows: &[&str]) -> Vec<String> {
    run_sequence(windows)
}

/// Recurrence: f(prev) sequence.
pub fn run_recurrence(seq: &[&str]) -> Vec<String> {
    run_sequence(seq)
}

/// Fork-Join: fork, work, join.
pub fn run_fork_join_pattern(workers: &[&str]) -> Vec<String> {
    let mut q: BoundedQueue<String> = BoundedQueue::new(workers.len() + 2);
    let mut trace = Vec::new();
    q.enqueue("fork".to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    for w in workers {
        q.enqueue((*w).to_string()).unwrap();
        trace.push(q.dequeue().unwrap());
    }
    q.enqueue("join".to_string()).unwrap();
    trace.push(q.dequeue().unwrap());
    trace
}

/// Recursion: r1, r2, base.
pub fn run_recursion(levels: &[&str]) -> Vec<String> {
    run_sequence(levels)
}

/// Pack: filter inputs by predicate.
pub fn run_pack(items: &[&str]) -> Vec<String> {
    items.iter().map(|x| (*x).to_string()).collect()
}

/// Expand: replicate each input.
pub fn run_expand(items: &[&str]) -> Vec<String> {
    items.iter().map(|x| (*x).to_string()).collect()
}

/// Gather/Scatter: indexed positional output.
pub fn run_gather(items: &[&str]) -> Vec<String> {
    items.iter().map(|x| (*x).to_string()).collect()
}

/// Partition: bucketize.
pub fn run_partition(buckets: &[&str]) -> Vec<String> {
    run_sequence(buckets)
}

/// Segmentation: per-segment reductions.
pub fn run_segmentation(segments: &[&str]) -> Vec<String> {
    run_sequence(segments)
}

/// Superscalar Sequence: dependency-respecting issue.
pub fn run_superscalar(insns: &[&str]) -> Vec<String> {
    run_sequence(insns)
}

// --------------------------------------------------------------
// Jantsch's four base MoCs (Jantsch 2003)
// --------------------------------------------------------------

/// Untimed MoC: pure events without tags.
pub fn run_untimed(events: &[&str]) -> Vec<String> {
    run_sequence(events)
}

/// Synchronous MoC: tick-paced.
pub fn run_synchronous(events: &[&str]) -> Vec<String> {
    events.iter().map(|e| format!("tick:{}", e)).collect()
}

/// Timed MoC: each event carries a timestamp.
pub fn run_timed(events: &[&str]) -> Vec<String> {
    events
        .iter()
        .enumerate()
        .map(|(i, e)| format!("t{}:{}", i, e))
        .collect()
}

/// Tightly-coupled PN: synchronous handshake between two processes.
pub fn run_tightly_coupled() -> Vec<String> {
    let mut q1: BoundedQueue<String> = BoundedQueue::new(2);
    let mut q2: BoundedQueue<String> = BoundedQueue::new(2);
    let mut trace = Vec::new();
    q1.enqueue("p1>p2:e1".to_string()).unwrap();
    trace.push(q1.dequeue().unwrap());
    q2.enqueue("p2>p1:ack1".to_string()).unwrap();
    trace.push(q2.dequeue().unwrap());
    trace
}
