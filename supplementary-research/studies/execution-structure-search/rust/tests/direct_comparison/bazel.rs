//! Direct comparison: Bazel.
//!
//! Writes a minimal Bazel workspace with three rules (compile, link,
//! bin), runs `bazel build //:bin --subcommands`, parses the action
//! order from stderr, and asserts equivalence with the `BuildDag`
//! topological order. Skips cleanly if `bazel` (or `bazelisk`) is not
//! installed.

use execution_modalities::workloads::build_dag::BuildDag;
use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn run() {
    let bazel_bin = match find_bazel() {
        Some(p) => p,
        None => {
            eprintln!("SKIP: bazel (or bazelisk) not installed at any known path; direct comparison cannot run");
            return;
        }
    };

    let version_line = match Command::new(&bazel_bin).arg("--version").output() {
        Ok(out) if out.status.success() => String::from_utf8_lossy(&out.stdout)
            .lines()
            .next()
            .unwrap_or("bazel")
            .to_string(),
        _ => {
            eprintln!("SKIP: bazel at {} failed to execute", bazel_bin.display());
            return;
        }
    };
    eprintln!(
        "compared against installed bazel ({}): {}",
        bazel_bin.display(),
        version_line
    );

    let dir: PathBuf = env::temp_dir().join(format!(
        "em_bazel_compare_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    fs::create_dir_all(&dir).expect("create tempdir");

    // WORKSPACE marker for legacy Bazel; MODULE.bazel for Bzlmod.
    fs::write(dir.join("WORKSPACE"), "").unwrap();
    fs::write(dir.join("MODULE.bazel"), "module(name = \"em_bazel\")\n").unwrap();

    // Three genrules: compile -> link -> bin.
    let build_file = "\
genrule(
    name = \"compile\",
    outs = [\"compile.out\"],
    cmd = \"echo compile > $@\",
)

genrule(
    name = \"link\",
    srcs = [\":compile\"],
    outs = [\"link.out\"],
    cmd = \"echo link > $@ && cat $(location :compile) >> $@\",
)

genrule(
    name = \"bin\",
    srcs = [\":link\"],
    outs = [\"bin.out\"],
    cmd = \"echo bin > $@ && cat $(location :link) >> $@\",
)
";
    fs::write(dir.join("BUILD.bazel"), build_file).unwrap();

    let out = Command::new(&bazel_bin)
        .arg("build")
        .arg("//:bin")
        .arg("--subcommands")
        .arg("--noshow_progress")
        .arg("--curses=no")
        .current_dir(&dir)
        .output()
        .expect("run bazel build");
    if !out.status.success() {
        eprintln!(
            "SKIP: bazel build failed (likely environment issue): stderr tail = {}",
            String::from_utf8_lossy(&out.stderr)
                .lines()
                .rev()
                .take(5)
                .collect::<Vec<_>>()
                .join(" | ")
        );
        let _ = fs::remove_dir_all(&dir);
        return;
    }

    let stderr = String::from_utf8_lossy(&out.stderr);
    let bazel_order = parse_action_order(&stderr);

    let dag = BuildDag::small_example();
    let our_order = topological_order(&dag);

    assert_eq!(
        bazel_order, our_order,
        "bazel action order {:?} differs from BuildDag order {:?}",
        bazel_order, our_order
    );
    eprintln!(
        "PASS: bazel action order = our reproduction order = {:?}",
        bazel_order
    );

    let _ = fs::remove_dir_all(&dir);
}

fn find_bazel() -> Option<PathBuf> {
    for cand in &["bazel", "bazelisk"] {
        if Command::new(cand)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            return Some(PathBuf::from(cand));
        }
    }
    let static_paths: &[&str] = &[
        "C:/Program Files/Bazel/bazel.exe",
        "C:/ProgramData/chocolatey/bin/bazel.exe",
        "/usr/bin/bazel",
        "/usr/local/bin/bazel",
        "/opt/homebrew/bin/bazel",
    ];
    for p in static_paths {
        if Path::new(p).exists() {
            return Some(PathBuf::from(p));
        }
    }
    None
}

/// Bazel --subcommands prints lines like:
///   SUBCOMMAND: # //:compile [action 'Executing genrule //:compile']
/// The rule name is extracted from each SUBCOMMAND line.
fn parse_action_order(stderr: &str) -> Vec<String> {
    let mut order: Vec<String> = Vec::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for line in stderr.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with("SUBCOMMAND:") {
            continue;
        }
        for tok in trimmed.split_whitespace() {
            if let Some(rest) = tok.strip_prefix("//:") {
                let name: String = rest
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                if !name.is_empty() && seen.insert(name.clone()) {
                    order.push(name);
                }
            }
        }
    }
    order
}

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
            let ready = node
                .inputs
                .iter()
                .all(|i| dag.source_contents.contains_key(i) || done.contains(i));
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
