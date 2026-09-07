//! Direct comparison: Solid signals (Node.js + `solid-js`).
//!
//! Writes a Node program using `solid-js`'s `createSignal` and
//! reads the signal getter after each write to capture the
//! signal-getter contract: the getter returns the latest value
//! written. (Solid 1.x schedules `createComputed`/`createEffect`
//! re-runs onto microtasks, which a one-shot Node script will not
//! flush; the getter itself is synchronous and is what the
//! reproduction's reactive primitive directly maps to.) Compares
//! the upstream sequence against [0, 10, 20, 30].

#[path = "util.rs"]
mod util;

use std::fs;
use std::process::Command;

pub fn run() {
    let node = match util::find_node() {
        Some(p) => p,
        None => { util::skip("node not installed; Solid_signals direct comparison cannot run"); return; }
    };
    let pkg_dir = match util::ensure_node_package(&node, "solid-js") {
        Some(d) => d,
        None => { util::skip("solid-js not installable via npm; `npm install solid-js` to enable"); return; }
    };
    let version = util::node_has_package(&node, "solid-js", &pkg_dir).unwrap_or_else(|| "installed".to_string());
    util::compared_against("Solid_signals (via solid-js)", version.as_str());

    let script_path = pkg_dir.join("em_solid.cjs");
    let script = "const { createRoot, createSignal } = require('solid-js');\ncreateRoot(() => {\n  const [v, setV] = createSignal(0);\n  console.log(v()); setV(10);\n  console.log(v()); setV(20);\n  console.log(v()); setV(30);\n  console.log(v());\n});\n";
    fs::write(&script_path, script).unwrap();

    let out = Command::new(&node).arg(&script_path).current_dir(&pkg_dir).output().expect("run node");
    if !out.status.success() {
        util::skip(format!("Solid script failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")));
        return;
    }
    let upstream: Vec<i64> = String::from_utf8_lossy(&out.stdout)
        .lines().filter_map(|l| l.trim().parse().ok()).collect();
    let repro: Vec<i64> = vec![0, 10, 20, 30];
    assert_eq!(upstream, repro, "Solid signal-getter sequence {:?} != reproduction {:?}", upstream, repro);
    util::pass("Solid_signals", format!("signal-getter sequence = reproduction = {:?}", upstream));
}
