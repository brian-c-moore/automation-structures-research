//! Bridge to the idiomatic Python reference oracles.
//!
//! One Python process per *algorithm* (not per input), talking JSON
//! over stdin/stdout: the request carries the whole input batch so the
//! property-test input batches stay feasible across the corpus.
//! The oracle runtime is deliberately independent of the Rust primitive
//! implementations under test. Every algorithm uses this bridge, and
//! `python/oracles.py` dispatches the request by algorithm name.

use crate::value::Value;
use std::io::Write;
use std::process::{Command, Stdio};

fn oracles_py() -> String {
    format!("{}/python/oracles.py", env!("CARGO_MANIFEST_DIR"))
}

/// Run the Python oracle for `algo` over every input, returning one
/// output per input in order.
pub fn run_batch(algo: &str, inputs: &[Value]) -> Vec<Value> {
    let batch = Value::List(inputs.to_vec()).to_json();
    let request = format!(r#"{{"algo":{:?},"inputs":{}}}"#, algo, batch);
    let python = std::env::var_os("PYTHON").unwrap_or_else(|| "python".into());
    let mut child = Command::new(&python)
        .arg(oracles_py())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|error| {
            panic!(
                "failed to spawn Python oracle interpreter {python:?}; set PYTHON to an executable path: {error}"
            )
        });
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(request.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    if !out.status.success() {
        panic!(
            "python oracle `{algo}` failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    match Value::from_json(stdout.trim()) {
        Value::List(v) => v,
        other => panic!("oracle `{algo}` did not return a list: {other:?}"),
    }
}
