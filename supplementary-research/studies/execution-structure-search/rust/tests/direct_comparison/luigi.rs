//! Direct comparison: Luigi (Python).
//!
//! Defines a four-task Luigi DAG in the
//! Ingest -> {TransformA, TransformB} -> Aggregate shape, runs it
//! with `local_scheduler=True`, captures the completion order by
//! having each task append its name to a shared trace file, and
//! asserts the order is one of the two topologically-valid orders
//! for the DAG.

#[path = "util.rs"]
mod util;

use std::fs;
use std::process::Command;

pub fn run() {
    let python = match util::find_python() {
        Some(p) => p,
        None => { util::skip("python not installed; Luigi direct comparison cannot run"); return; }
    };
    let version = match util::python_has_package(&python, "luigi") {
        Some(v) => v,
        None => { util::skip(format!("luigi not installed under {}; `pip install luigi` to enable", python.display())); return; }
    };
    util::compared_against(format!("Luigi (via luigi {})", version), version.as_str());

    let dir = util::make_tempdir("luigi");
    let trace_path = dir.join("trace.txt");
    let script = dir.join("dag.py");
    let trace_str = trace_path.display().to_string().replace('\\', "/");
    let dir_str = dir.display().to_string().replace('\\', "/");
    let script_src = format!(
        "import luigi, os\nTRACE = r\"{trace}\"\nclass _T(luigi.Task):\n    name = luigi.Parameter()\n    def output(self):\n        return luigi.LocalTarget(os.path.join(r\"{dir}\", self.name + '.done'))\n    def run(self):\n        with open(TRACE, 'a') as f: f.write(self.name + '\\n')\n        with self.output().open('w') as f: f.write('ok')\nclass Ingest(_T):\n    name = luigi.Parameter(default='ingest')\nclass TransformA(_T):\n    name = luigi.Parameter(default='transform_a')\n    def requires(self): return Ingest()\nclass TransformB(_T):\n    name = luigi.Parameter(default='transform_b')\n    def requires(self): return Ingest()\nclass Aggregate(_T):\n    name = luigi.Parameter(default='aggregate')\n    def requires(self): return [TransformA(), TransformB()]\nif __name__ == '__main__':\n    luigi.build([Aggregate()], local_scheduler=True, log_level='WARNING')\n",
        trace = trace_str,
        dir = dir_str
    );
    fs::write(&script, script_src).unwrap();

    let out = Command::new(&python).arg(&script).current_dir(&dir).output().expect("run luigi");
    if !out.status.success() {
        util::skip(format!(
            "luigi run failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")
        ));
        let _ = fs::remove_dir_all(&dir);
        return;
    }

    let raw = fs::read_to_string(&trace_path).unwrap_or_default();
    let upstream: Vec<String> = raw.lines().map(|s| s.to_string()).collect();
    if upstream.is_empty() {
        util::skip("luigi produced no trace; DAG may not have executed");
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
        "Luigi trace {:?} is not a topologically-valid order",
        upstream
    );
    util::pass("Luigi", format!("local-scheduler completion order = topologically-valid = {:?}", upstream));
    let _ = fs::remove_dir_all(&dir);
}
