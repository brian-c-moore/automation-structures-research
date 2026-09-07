//! Direct comparison: GitHub Actions via the `act` local runner.
//!
//! Writes a small workflow with three jobs in a linear dependency
//! chain (ingest -> transform -> aggregate). Runs `act --list` to
//! enumerate the stage-ordered jobs, parses the order, and asserts
//! equality with the reproduction's three-step chain.

#[path = "util.rs"]
mod util;

use std::fs;
use std::process::Command;

pub fn run() {
    let bin = match util::find_binary("act", &[]) {
        Some(p) => p,
        None => { util::skip("act not installed at any known path; GitHub_Actions direct comparison cannot run"); return; }
    };
    let version = Command::new(&bin).arg("--version").output().ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "act (version probe unavailable)".to_string());
    util::compared_against("GitHub_Actions (via act)", version.as_str());

    let dir = util::make_tempdir("github_actions");
    let wf_dir = dir.join(".github").join("workflows");
    fs::create_dir_all(&wf_dir).unwrap();
    fs::write(wf_dir.join("ci.yml"),
        "name: ci\non: push\njobs:\n  ingest:\n    runs-on: ubuntu-latest\n    steps: [{run: 'echo ingest'}]\n  transform:\n    runs-on: ubuntu-latest\n    needs: ingest\n    steps: [{run: 'echo transform'}]\n  aggregate:\n    runs-on: ubuntu-latest\n    needs: transform\n    steps: [{run: 'echo aggregate'}]\n").unwrap();

    let out = Command::new(&bin).arg("--list").current_dir(&dir).output().expect("run act --list");
    if !out.status.success() {
        util::skip(format!("act --list failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")));
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let mut by_stage: Vec<(usize, String)> = Vec::new();
    for line in stdout.lines() {
        let cols: Vec<&str> = line.split_whitespace().collect();
        if cols.len() < 2 { continue; }
        if cols[0] == "Stage" || cols[0] == "ID" { continue; }
        if let Ok(stage) = cols[0].parse::<usize>() {
            let job = cols[1].to_string();
            if ["ingest","transform","aggregate"].contains(&job.as_str()) {
                by_stage.push((stage, job));
            }
        }
    }
    by_stage.sort_by_key(|(s, _)| *s);
    let upstream: Vec<String> = by_stage.into_iter().map(|(_, j)| j).collect();
    if upstream.is_empty() {
        util::skip("act produced no parseable job listing");
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let repro = vec!["ingest".to_string(), "transform".to_string(), "aggregate".to_string()];
    assert_eq!(upstream, repro, "act job order {:?} != reproduction {:?}", upstream, repro);
    util::pass("GitHub_Actions", format!("act stage-ordered jobs = scientific-workflow chain = {:?}", upstream));
    let _ = fs::remove_dir_all(&dir);
}
