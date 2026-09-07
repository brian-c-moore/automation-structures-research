//! Direct comparison: Tekton Pipelines (`tkn` CLI).
//!
//! Tekton's actual pipeline execution runs in a Kubernetes cluster;
//! `tkn` is a thin CLI client to the in-cluster controller. The CLI
//! ships `tkn pipeline list/describe`, `tkn taskrun`, etc — all
//! require cluster access. Without a cluster, the structural test is
//! that the CLI exposes its core subcommands (`pipeline`, `task`,
//! `pipelinerun`, `taskrun`) that map to the reproduction's
//! pipeline-step graph.

#[path = "util.rs"]
mod util;

use std::process::Command;

pub fn run() {
    let bin = match util::find_binary("tkn", &[]) {
        Some(p) => p,
        None => { util::skip("tkn not installed at any known path; Tekton direct comparison cannot run"); return; }
    };
    let version = Command::new(&bin).arg("version").output().ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.lines().next().map(|x| x.to_string()))
        .unwrap_or_else(|| "tkn (version probe unavailable)".to_string());
    util::compared_against("Tekton (via tkn)", version.as_str());

    let help = Command::new(&bin).arg("--help").output().expect("tkn --help");
    let txt = format!("{}{}", String::from_utf8_lossy(&help.stdout), String::from_utf8_lossy(&help.stderr));
    for sub in &["pipeline", "task", "pipelinerun", "taskrun"] {
        assert!(txt.contains(sub),
            "tkn --help missing expected subcommand {}; got: {}",
            sub, txt.lines().take(15).collect::<Vec<_>>().join(" | "));
    }
    util::pass("Tekton", format!("tkn {} exposes pipeline/task/pipelinerun/taskrun subcommands = reproduction step-graph stages", version));
}
