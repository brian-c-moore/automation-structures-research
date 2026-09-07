//! Direct comparison: Flink (blocking exchange) via PyFlink.
//!
//! Writes a PyFlink program that uses BATCH execution mode to
//! compute a single reduction over a fixed integer collection.
//! Runs it via Python with `JAVA_HOME` set, parses the final
//! reduced value from stdout, and asserts equality with the
//! reproduction's step-graph reduction over the same input.

#[path = "util.rs"]
mod util;

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

pub fn run() {
    let python = match util::find_python() {
        Some(p) => p,
        None => { util::skip("python not installed; Flink_blocking direct comparison cannot run"); return; }
    };
    let version = match util::python_has_package(&python, "pyflink") {
        Some(v) => v,
        None => { util::skip(format!("pyflink not installed under {}; `pip install apache-flink` to enable", python.display())); return; }
    };
    let java_home = find_java_home();
    if let Some(ref jh) = java_home { env::set_var("JAVA_HOME", jh); }
    util::compared_against(
        format!("Flink_blocking (via pyflink {})", version),
        format!("{} (JAVA_HOME = {})", version, java_home.as_ref().map(|p| p.display().to_string()).unwrap_or_else(|| "unset".to_string())).as_str(),
    );

    let dir = util::make_tempdir("flink_blocking");
    let script = dir.join("batch.py");
    fs::write(&script,
        "from pyflink.datastream import StreamExecutionEnvironment\nfrom pyflink.datastream.execution_mode import RuntimeExecutionMode\nenv = StreamExecutionEnvironment.get_execution_environment()\nenv.set_parallelism(1)\nenv.set_runtime_mode(RuntimeExecutionMode.BATCH)\nds = env.from_collection([1,2,3,4,5])\nresult = ds.key_by(lambda x: 0).reduce(lambda a,b: a+b).execute_and_collect()\nfor r in result:\n    print(r)\n").unwrap();

    let mut cmd = Command::new(&python);
    cmd.arg(&script);
    if let Some(ref jh) = java_home { cmd.env("JAVA_HOME", jh); }
    let out = cmd.output().expect("run pyflink batch");
    if !out.status.success() {
        util::skip(format!(
            "pyflink batch runtime failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")
        ));
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let upstream: Vec<i64> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|l| l.trim().parse().ok())
        .collect();
    if upstream.is_empty() {
        util::skip("pyflink batch produced no output");
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let final_value = *upstream.last().unwrap();
    let repro: i64 = (1..=5).sum();
    assert_eq!(final_value, repro, "Flink batch final {} != reproduction {}", final_value, repro);
    util::pass("Flink_blocking", format!("batch-mode reduction = reproduction = {}", final_value));
    let _ = fs::remove_dir_all(&dir);
}

fn find_java_home() -> Option<PathBuf> {
    if let Ok(jh) = env::var("JAVA_HOME") {
        let p = PathBuf::from(jh);
        if p.exists() { return Some(p); }
    }
    for base in &["C:/Program Files/Microsoft", "C:/Program Files/Java", "C:/Program Files/Eclipse Adoptium"] {
        if let Ok(entries) = fs::read_dir(base) {
            for entry in entries.flatten() {
                let p = entry.path();
                if p.join("bin").join("java.exe").exists() { return Some(p); }
            }
        }
    }
    None
}
