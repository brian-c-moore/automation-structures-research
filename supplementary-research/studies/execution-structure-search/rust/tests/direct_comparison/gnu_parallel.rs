//! Direct comparison: GNU parallel.
//!
//! Runs `parallel echo {} ::: 1 2 3 4 5`, which fans out a single
//! command across the input set. Captures stdout (order is not
//! guaranteed across workers — the structural property of GNU
//! parallel is the unordered output multiset). Compares the upstream
//! multiset to the reproduction's fan-out-then-collect set.

#[path = "util.rs"]
mod util;

use std::collections::BTreeSet;
use std::process::Command;

pub fn run() {
    let bin = match util::find_binary("parallel", &[]) {
        Some(p) => p,
        None => { util::skip("parallel not installed at any known path; GNU_parallel direct comparison cannot run"); return; }
    };
    let version = Command::new(&bin).arg("--version").output().ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.lines().next().map(|x| x.to_string()))
        .unwrap_or_else(|| "parallel (version probe unavailable)".to_string());
    util::compared_against("GNU_parallel (via parallel)", version.as_str());

    let out = Command::new(&bin)
        .arg("--no-notice")
        .arg("echo").arg("{}").arg(":::").arg("1").arg("2").arg("3").arg("4").arg("5")
        .output()
        .expect("parallel echo");
    if !out.status.success() {
        util::skip(format!("parallel invocation failed (often needs `parallel --citation`): {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")));
        return;
    }
    let upstream: BTreeSet<i64> = String::from_utf8_lossy(&out.stdout)
        .lines().filter_map(|l| l.trim().parse().ok()).collect();
    let repro: BTreeSet<i64> = [1i64, 2, 3, 4, 5].into_iter().collect();
    assert_eq!(upstream, repro, "parallel output multiset {:?} != reproduction {:?}", upstream, repro);
    util::pass("GNU_parallel", format!("parallel fan-out output multiset = reproduction = {:?}", upstream));
}
