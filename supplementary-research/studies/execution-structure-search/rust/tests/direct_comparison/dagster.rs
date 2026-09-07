//! Direct comparison: Dagster (Python).
//!
//! Defines a Dagster job with four ops in the same DAG shape,
//! executes it via `the_job.execute_in_process()`, captures op
//! execution order from each op's print statements, and asserts a
//! topologically valid order.

#[path = "util.rs"]
mod util;

use std::collections::HashSet;
use std::fs;
use std::process::Command;

pub fn run() {
    let python = match util::find_python() {
        Some(p) => p,
        None => { util::skip("python not installed; Dagster direct comparison cannot run"); return; }
    };
    let version = match util::python_has_package(&python, "dagster") {
        Some(v) => v,
        None => { util::skip(format!("dagster not installed under {}; `pip install dagster` to enable", python.display())); return; }
    };
    util::compared_against(format!("Dagster (via dagster {})", version), version.as_str());

    let dir = util::make_tempdir("dagster");
    let script = dir.join("job.py");
    fs::write(&script, "from dagster import op, job\nimport sys\n@op\ndef ingest():\n    print('ingest', flush=True); return 'ingest'\n@op\ndef transform_a(_x):\n    print('transform_a', flush=True); return 'transform_a'\n@op\ndef transform_b(_x):\n    print('transform_b', flush=True); return 'transform_b'\n@op\ndef aggregate(_a, _b):\n    print('aggregate', flush=True)\n@job\ndef the_job():\n    i = ingest()\n    a = transform_a(i)\n    b = transform_b(i)\n    aggregate(a, b)\nif __name__ == '__main__':\n    r = the_job.execute_in_process()\n    sys.exit(0 if r.success else 1)\n").unwrap();

    let out = Command::new(&python)
        .arg(&script)
        .current_dir(&dir)
        .env("DAGSTER_HOME", dir.to_str().unwrap_or("."))
        .output()
        .expect("run dagster");
    if !out.status.success() {
        util::skip(format!(
            "dagster run failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")
        ));
        let _ = fs::remove_dir_all(&dir);
        return;
    }

    let interest: HashSet<&str> = ["ingest","transform_a","transform_b","aggregate"].into_iter().collect();
    let upstream: Vec<String> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|s| s.trim())
        .filter(|s| interest.contains(*s))
        .map(|s| s.to_string())
        .collect();
    if upstream.is_empty() {
        util::skip("dagster produced no op trace");
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let valid: Vec<Vec<&str>> = vec![
        vec!["ingest","transform_a","transform_b","aggregate"],
        vec!["ingest","transform_b","transform_a","aggregate"],
    ];
    let upstream_refs: Vec<&str> = upstream.iter().map(|s| s.as_str()).collect();
    assert!(
        valid.iter().any(|o| *o == upstream_refs),
        "Dagster trace {:?} is not a topologically-valid order",
        upstream
    );
    util::pass("Dagster", format!("op execution order = topologically-valid = {:?}", upstream));
    let _ = fs::remove_dir_all(&dir);
}
