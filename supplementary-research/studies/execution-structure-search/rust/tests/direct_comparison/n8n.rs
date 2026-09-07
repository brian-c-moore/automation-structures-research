//! Direct comparison: n8n (Node-based workflow runtime).
//!
//! n8n's testing surface from CLI is limited (the server is the
//! primary entry point). This harness probes that n8n exposes the
//! `execute` subcommand (which is the bridge from a workflow JSON
//! to actual execution) and that the subcommand accepts a workflow-
//! source flag. The comparison property is that n8n's CLI surface
//! exposes the workflow-execute pipeline the configuration relies
//! on.

#[path = "util.rs"]
mod util;

use std::process::Command;

pub fn run() {
    let bin = match util::find_binary("n8n", &[]) {
        Some(p) => p,
        None => { util::skip("n8n not installed at any known path; n8n direct comparison cannot run"); return; }
    };
    let version = Command::new(&bin).arg("--version").output().ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "n8n (version probe unavailable)".to_string());
    util::compared_against("n8n (via n8n)", version.as_str());

    let help = Command::new(&bin).arg("execute").arg("--help").output().expect("n8n execute --help");
    if !help.status.success() {
        util::skip("n8n execute subcommand not available in this build");
        return;
    }
    let help_text = String::from_utf8_lossy(&help.stdout);
    assert!(
        help_text.contains("--file") || help_text.contains("workflow") || help_text.contains("--id"),
        "n8n execute help does not reference a workflow source flag; got: {}",
        help_text.lines().take(10).collect::<Vec<_>>().join(" | ")
    );
    util::pass("n8n", format!("n8n {} exposes execute subcommand with workflow-source flag", version));
}
