//! Direct comparison: Prefect (Python).
//!
//! Defines a Prefect flow with four tasks in the same DAG shape,
//! runs it in-process, captures task completion order from each
//! task's print statements, and asserts a topologically valid order.

#[path = "util.rs"]
mod util;

use std::collections::HashSet;
use std::fs;
use std::process::Command;

pub fn run() {
    let python = match util::find_python() {
        Some(p) => p,
        None => { util::skip("python not installed; Prefect direct comparison cannot run"); return; }
    };
    let version = match util::python_has_package(&python, "prefect") {
        Some(v) => v,
        None => { util::skip(format!("prefect not installed under {}; `pip install prefect` to enable", python.display())); return; }
    };
    util::compared_against(format!("Prefect (via prefect {})", version), version.as_str());

    let dir = util::make_tempdir("prefect");
    let script = dir.join("flow.py");
    fs::write(&script, "import os\nos.environ['PREFECT_LOGGING_LEVEL'] = 'WARNING'\nfrom prefect import flow, task\n@task\ndef ingest():\n    print('ingest', flush=True); return 'ingest'\n@task\ndef transform_a(_x):\n    print('transform_a', flush=True); return 'transform_a'\n@task\ndef transform_b(_x):\n    print('transform_b', flush=True); return 'transform_b'\n@task\ndef aggregate(_a, _b):\n    print('aggregate', flush=True)\n@flow\ndef the_flow():\n    i = ingest()\n    a = transform_a(i)\n    b = transform_b(i)\n    aggregate(a, b)\nif __name__ == '__main__':\n    the_flow()\n").unwrap();

    let out = Command::new(&python).arg(&script).current_dir(&dir).output().expect("run prefect");
    if !out.status.success() {
        util::skip(format!(
            "prefect flow failed: {}",
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
        util::skip("prefect produced no task trace");
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
        "Prefect trace {:?} is not a topologically-valid order",
        upstream
    );
    util::pass("Prefect", format!("flow task completion order = topologically-valid = {:?}", upstream));
    let _ = fs::remove_dir_all(&dir);
}
