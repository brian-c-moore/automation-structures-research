//! Direct comparison: Make.
//!
//! Writes a Makefile with three echo-only rules (compile -> link ->
//! bin) into a tempdir, runs `make bin`, captures the build order
//! from stdout, then runs the `BuildDag::small_example()` reproduction
//! and asserts the topological build orders match. If `make` cannot
//! be found at any known path, the test prints a SKIP line and
//! returns cleanly.

use execution_modalities::workloads::build_dag::BuildDag;
use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn run() {
    let make_bin = match find_make() {
        Some(p) => p,
        None => {
            eprintln!("SKIP: make not installed at any known path; direct comparison cannot run");
            return;
        }
    };

    let version_line = match Command::new(&make_bin).arg("--version").output() {
        Ok(out) if out.status.success() => String::from_utf8_lossy(&out.stdout)
            .lines()
            .next()
            .unwrap_or("make")
            .to_string(),
        _ => {
            eprintln!(
                "SKIP: make at {} failed to execute",
                make_bin.display()
            );
            return;
        }
    };
    eprintln!(
        "compared against installed make ({}): {}",
        make_bin.display(),
        version_line
    );

    let dir: PathBuf = env::temp_dir().join(format!(
        "em_make_compare_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    fs::create_dir_all(&dir).expect("create tempdir");

    let makefile_path = dir.join("Makefile");
    let makefile = "\
.PHONY: bin link compile

bin: link
\t@echo bin

link: compile
\t@echo link

compile:
\t@echo compile
";
    fs::write(&makefile_path, makefile).expect("write Makefile");

    let out = Command::new(&make_bin)
        .arg("-B")
        .arg("-f")
        .arg(&makefile_path)
        .arg("bin")
        .current_dir(&dir)
        .output()
        .expect("run make");
    assert!(out.status.success(), "make exited non-zero: {:?}", out);

    let make_order: Vec<String> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect();

    let dag = BuildDag::small_example();
    let our_order = topological_order(&dag);

    assert_eq!(
        make_order, our_order,
        "real make build order {:?} differs from BuildDag order {:?}",
        make_order, our_order
    );
    eprintln!(
        "PASS: real make order = our reproduction order = {:?}",
        make_order
    );

    let _ = fs::remove_dir_all(&dir);
}

/// Search PATH and a list of well-known install locations for a
/// working `make`.
fn find_make() -> Option<PathBuf> {
    if Command::new("make").arg("--version").output().map(|o| o.status.success()).unwrap_or(false) {
        return Some(PathBuf::from("make"));
    }
    let static_paths: &[&str] = &[
        // Windows install locations
        "C:/Program Files/Git/usr/bin/make.exe",
        "C:/Program Files/Git/mingw64/bin/mingw32-make.exe",
        "C:/Program Files (x86)/GnuWin32/bin/make.exe",
        "C:/msys64/usr/bin/make.exe",
        "C:/cygwin64/bin/make.exe",
        "C:/ProgramData/chocolatey/bin/make.exe",
        "C:/Strawberry/c/bin/gmake.exe",
        // Unix install locations
        "/usr/bin/make",
        "/usr/local/bin/make",
        "/opt/homebrew/bin/make",
    ];
    for p in static_paths {
        if Path::new(p).exists() {
            return Some(PathBuf::from(p));
        }
    }
    // WinGet packages directory: search for ezwinports.make or GnuWin32.Make.
    if let Ok(local) = env::var("LOCALAPPDATA") {
        let pkgs = PathBuf::from(local).join("Microsoft").join("WinGet").join("Packages");
        if let Ok(entries) = fs::read_dir(&pkgs) {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().to_string();
                if name.starts_with("ezwinports.make")
                    || name.starts_with("GnuWin32.Make")
                {
                    for candidate in [
                        entry.path().join("bin").join("make.exe"),
                        entry.path().join("make.exe"),
                    ] {
                        if candidate.exists() {
                            return Some(candidate);
                        }
                    }
                }
            }
        }
    }
    None
}

/// Topological order of the `BuildDag`'s nodes, starting from the
/// leaves (sources). Returns the names in the order they would
/// execute under a step-based DAG runner.
fn topological_order(dag: &BuildDag) -> Vec<String> {
    let mut order: Vec<String> = Vec::new();
    let mut done: BTreeSet<String> = BTreeSet::new();
    let nodes: Vec<&String> = dag.nodes.keys().collect();
    while order.len() < nodes.len() {
        let mut progressed = false;
        for n in &nodes {
            if done.contains(*n) {
                continue;
            }
            let node = &dag.nodes[*n];
            let ready = node.inputs.iter().all(|i| {
                dag.source_contents.contains_key(i) || done.contains(i)
            });
            if ready {
                order.push((*n).clone());
                done.insert((*n).clone());
                progressed = true;
            }
        }
        assert!(progressed, "DAG has unresolved dependencies");
    }
    order
}
