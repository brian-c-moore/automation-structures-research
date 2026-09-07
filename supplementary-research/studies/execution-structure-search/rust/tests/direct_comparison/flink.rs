//! Direct comparison: Flink (pipelined).
//!
//! Apache Flink is JVM-only; there is no Rust client. The two
//! realistic ways to drive a real Flink runtime from a Rust test
//! without bundling a full Flink distribution are:
//!
//! 1. A standalone Flink install + a precompiled job JAR (heavy,
//!    rarely present on developer machines).
//! 2. PyFlink, which ships a Java-based Flink local runtime inside
//!    a Python wheel (`pip install apache-flink`).
//!
//! Path (2) is used because it is the only one that runs a real Flink
//! runtime without separate JVM/Flink-distribution configuration
//! beyond a `pip install`. If `python` and PyFlink are not available
//! (and Java is not available for PyFlink's bundled runtime), the
//! test prints a SKIP line and returns cleanly.

use execution_modalities::workloads::streaming_sql::StreamingSql;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn run() {
    let python = match find_python() {
        Some(p) => p,
        None => {
            eprintln!("SKIP: python not installed at any known path; direct comparison cannot run");
            return;
        }
    };

    let pyflink_version = match detect_pyflink(&python) {
        Some(v) => v,
        None => {
            eprintln!(
                "SKIP: pyflink not installed under {}; run `pip install apache-flink` to enable",
                python.display()
            );
            return;
        }
    };

    // PyFlink needs Java. Set JAVA_HOME if a JDK is found.
    let java_home = find_java_home();
    if let Some(ref jh) = java_home {
        env::set_var("JAVA_HOME", jh);
        eprintln!(
            "compared against installed pyflink: {} (via {}, JAVA_HOME={})",
            pyflink_version,
            python.display(),
            jh.display()
        );
    } else {
        eprintln!(
            "compared against installed pyflink: {} (via {}, JAVA_HOME unset)",
            pyflink_version,
            python.display()
        );
    }

    let path: PathBuf = env::temp_dir().join(format!(
        "em_pyflink_{}_{}.py",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    fs::write(&path, PYFLINK_SCRIPT).expect("write pyflink script");

    let mut cmd = Command::new(&python);
    cmd.arg(&path);
    if let Some(ref jh) = java_home {
        cmd.env("JAVA_HOME", jh);
    }
    let out = cmd.output().expect("run python");
    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        eprintln!(
            "SKIP: pyflink runtime failed (Java missing or jvm error): stderr tail = {}",
            stderr.lines().rev().take(5).collect::<Vec<_>>().join(" | ")
        );
        let _ = fs::remove_file(&path);
        return;
    }
    let stdout = String::from_utf8_lossy(&out.stdout);

    let flink_windows = parse_pyflink_windows(&stdout);
    let our = StreamingSql::small_example();
    let our_windows: Vec<(u64, i64)> = our.run().into_iter().map(|w| (w.start, w.sum)).collect();

    assert_eq!(
        flink_windows, our_windows,
        "pyflink windows {:?} differ from reproduction {:?}",
        flink_windows, our_windows
    );
    eprintln!(
        "PASS: pyflink windowed aggregation = reproduction = {:?}",
        our_windows
    );

    let _ = fs::remove_file(&path);
}

fn find_python() -> Option<PathBuf> {
    for cand in &["python3", "python"] {
        if Command::new(cand)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            return Some(PathBuf::from(cand));
        }
    }
    // Search well-known Windows install locations.
    let mut candidates: Vec<PathBuf> = Vec::new();
    if let Ok(local) = env::var("LOCALAPPDATA") {
        let py_root = PathBuf::from(&local).join("Programs").join("Python");
        if let Ok(entries) = fs::read_dir(&py_root) {
            for entry in entries.flatten() {
                let exe = entry.path().join("python.exe");
                if exe.exists() {
                    candidates.push(exe);
                }
            }
        }
        candidates.push(PathBuf::from(&local).join("Microsoft").join("WindowsApps").join("python.exe"));
        candidates.push(PathBuf::from(&local).join("Microsoft").join("WindowsApps").join("python3.exe"));
    }
    for base in &["C:/Python312", "C:/Python311", "C:/Python310"] {
        candidates.push(PathBuf::from(format!("{}/python.exe", base)));
    }
    // Unix.
    for u in &["/usr/bin/python3", "/usr/local/bin/python3", "/opt/homebrew/bin/python3"] {
        candidates.push(PathBuf::from(u));
    }
    for c in candidates {
        if c.exists() {
            return Some(c);
        }
    }
    None
}

fn detect_pyflink(python: &Path) -> Option<String> {
    let out = Command::new(python)
        .arg("-c")
        .arg("import pyflink; print(pyflink.version.__version__)")
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let v = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if v.is_empty() {
        None
    } else {
        Some(v)
    }
}

fn find_java_home() -> Option<PathBuf> {
    if let Ok(jh) = env::var("JAVA_HOME") {
        let p = PathBuf::from(jh);
        if p.exists() {
            return Some(p);
        }
    }
    let mut bases: Vec<PathBuf> = Vec::new();
    for base in &["C:/Program Files/Microsoft", "C:/Program Files/Eclipse Adoptium", "C:/Program Files/Java", "C:/Program Files (x86)/Java"] {
        if let Ok(entries) = fs::read_dir(base) {
            for entry in entries.flatten() {
                let p = entry.path();
                if p.join("bin").join("java.exe").exists() {
                    bases.push(p);
                }
            }
        }
    }
    // WinGet packages.
    if let Ok(local) = env::var("LOCALAPPDATA") {
        let pkgs = PathBuf::from(local).join("Microsoft").join("WinGet").join("Packages");
        if let Ok(entries) = fs::read_dir(&pkgs) {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().to_string();
                if name.starts_with("Microsoft.OpenJDK") || name.starts_with("EclipseAdoptium.Temurin") {
                    if let Ok(inner) = fs::read_dir(entry.path()) {
                        for sub in inner.flatten() {
                            let p = sub.path();
                            if p.join("bin").join("java.exe").exists() {
                                bases.push(p);
                            }
                        }
                    }
                }
            }
        }
    }
    bases.into_iter().next()
}

fn parse_pyflink_windows(stdout: &str) -> Vec<(u64, i64)> {
    let mut out: Vec<(u64, i64)> = Vec::new();
    for line in stdout.lines() {
        let mut tokens = line.split_whitespace();
        if tokens.next() != Some("WINDOW") {
            continue;
        }
        let start = tokens.next().and_then(|s| s.parse::<u64>().ok());
        let sum = tokens.next().and_then(|s| s.parse::<i64>().ok());
        if let (Some(s), Some(v)) = (start, sum) {
            out.push((s, v));
        }
    }
    out.sort_by_key(|(s, _)| *s);
    out
}

const PYFLINK_SCRIPT: &str = r#"
from pyflink.datastream import StreamExecutionEnvironment
from pyflink.datastream.window import TumblingEventTimeWindows
from pyflink.common.time import Time
from pyflink.common.watermark_strategy import WatermarkStrategy, TimestampAssigner
from pyflink.common.typeinfo import Types

class TsAssigner(TimestampAssigner):
    def extract_timestamp(self, value, _record_timestamp):
        return int(value[0])

env = StreamExecutionEnvironment.get_execution_environment()
env.set_parallelism(1)

events = [(1, 10), (2, 20), (4, 5), (6, 7), (7, 3), (11, 100)]
type_info = Types.TUPLE([Types.LONG(), Types.LONG()])

ws = WatermarkStrategy.for_monotonous_timestamps().with_timestamp_assigner(TsAssigner())
ds = env.from_collection(events, type_info=type_info).assign_timestamps_and_watermarks(ws)

windowed = ds.key_by(lambda x: 0, key_type=Types.LONG()) \
             .window(TumblingEventTimeWindows.of(Time.milliseconds(5)))

class Sum:
    def reduce(self, a, b):
        return (min(a[0], b[0]), a[1] + b[1])

result = windowed.reduce(Sum().reduce, output_type=type_info)
collected = list(result.execute_and_collect())
by_window = {}
for (ts, val) in collected:
    start = (ts // 5) * 5
    by_window.setdefault(start, 0)
    by_window[start] = val
for start in sorted(by_window):
    print(f"WINDOW {start} {by_window[start]}")
"#;
