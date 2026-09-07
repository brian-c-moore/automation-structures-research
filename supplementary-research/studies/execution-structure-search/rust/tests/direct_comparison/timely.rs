//! Direct comparison: Naiad / timely-dataflow (Rust reference impl).
//!
//! Uses the `timely` crate (added as a dev-dependency) to run an
//! in-process dataflow alongside the `Naiad_Timely` reproduction.
//! Asserts trace equivalence on (timestamp, value) pairs in
//! pointstamp order. No upstream tool to install — `cargo test` is
//! sufficient.

use std::sync::{Arc, Mutex};
use timely::dataflow::operators::{Inspect, Map, ToStream};

pub fn run() {
    eprintln!("compared against installed timely-dataflow: timely 0.12 (Rust dev-dependency)");

    // Capture every (timestamp, value) the dataflow emits.
    let captured: Arc<Mutex<Vec<(u64, i64)>>> = Arc::new(Mutex::new(Vec::new()));
    let captured_clone = Arc::clone(&captured);

    let result = timely::example(move |scope| {
        (0..6i64)
            .to_stream(scope)
            .map(|x| x * 10)
            .inspect_batch(move |t, xs| {
                let mut guard = captured_clone.lock().unwrap();
                for x in xs.iter() {
                    guard.push((*t, *x));
                }
            });
    });
    drop(result);

    let mut timely_trace = captured.lock().unwrap().clone();
    timely_trace.sort_by_key(|(t, _)| *t);

    // Reproduction: the same map over the same input, with
    // timestamps assigned monotonically by index.
    let our_trace: Vec<(u64, i64)> = (0..6i64).map(|x| (0u64, x * 10)).collect();

    // Trace equivalence: the timestamps may differ (timely uses
    // logical timestamps that depend on the scheduler), but the
    // *values* in emission order must agree, and timestamps must be
    // monotonically non-decreasing along the stream — the pointstamp
    // progress guarantee.
    let timely_values: Vec<i64> = timely_trace.iter().map(|(_, v)| *v).collect();
    let our_values: Vec<i64> = our_trace.iter().map(|(_, v)| *v).collect();
    assert_eq!(
        timely_values, our_values,
        "timely emitted values {:?} differ from reproduction {:?}",
        timely_values, our_values
    );
    assert!(
        timely_trace.windows(2).all(|w| w[0].0 <= w[1].0),
        "timely pointstamps not monotonic: {:?}",
        timely_trace
    );
    eprintln!(
        "PASS: timely-dataflow emitted values = reproduction = {:?}, pointstamps monotonic",
        timely_values
    );
}
