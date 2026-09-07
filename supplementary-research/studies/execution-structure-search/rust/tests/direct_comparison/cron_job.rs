//! Direct comparison: cron job (time-based trigger).
//!
//! POSIX `crontab` itself has no "evaluate this expression" mode;
//! its semantics is the user-table read/write surface (`-l`, `-e`).
//! The structural property of cron — "fire at scheduled wall-clock
//! instants matching the schedule" — is provided by `croniter`
//! (Python) which is the canonical reference implementation. This
//! harness uses `croniter` if available to compute the next five
//! fire times for `*/5 * * * *`, and asserts they form a five-minute
//! arithmetic progression. If neither `crontab` nor `croniter` is
//! available, skips cleanly.

#[path = "util.rs"]
mod util;

use std::process::Command;

pub fn run() {
    let _crontab_present = util::find_binary("crontab", &[]).is_some();
    let python = match util::find_python() {
        Some(p) => p,
        None => { util::skip("python not installed; cron_job direct comparison cannot run without croniter"); return; }
    };
    let version = match util::python_has_package(&python, "croniter") {
        Some(v) => v,
        None => { util::skip("croniter not installed under python; `pip install croniter` to enable"); return; }
    };
    util::compared_against("cron_job (via croniter)", version.as_str());

    let out = Command::new(&python)
        .arg("-c")
        .arg("from croniter import croniter; from datetime import datetime; base = datetime(2026,1,1,0,0,0); it = croniter('*/5 * * * *', base); [print(it.get_next(datetime).isoformat()) for _ in range(5)]")
        .output()
        .expect("run croniter");
    if !out.status.success() {
        util::skip(format!("croniter invocation failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")));
        return;
    }
    let lines: Vec<String> = String::from_utf8_lossy(&out.stdout)
        .lines().map(|s| s.trim().to_string()).collect();
    assert_eq!(lines.len(), 5, "Expected 5 fire times, got {:?}", lines);
    let times: Vec<&str> = lines.iter().map(|s| s.as_str()).collect();
    let expected = [
        "2026-01-01T00:05:00",
        "2026-01-01T00:10:00",
        "2026-01-01T00:15:00",
        "2026-01-01T00:20:00",
        "2026-01-01T00:25:00",
    ];
    assert_eq!(times, expected, "croniter fire times {:?} != reproduction {:?}", times, expected);
    util::pass("cron_job", format!("croniter '*/5 * * * *' fire times = 5-minute progression from 2026-01-01T00:00 = {:?}", expected));
}
