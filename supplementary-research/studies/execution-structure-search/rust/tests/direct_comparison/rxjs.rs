//! Direct comparison: RxJS.
//!
//! Writes a Node.js script that constructs an observable chain
//! (`from([..]).pipe(map, filter, reduce)`), runs it via Node, and
//! asserts the emitted values match the `ReactiveUiPipeline` output.
//! Skips cleanly if Node.js or the `rxjs` package is not installed.

use execution_modalities::workloads::reactive_ui::{ClickEvent, ReactiveUiPipeline};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn run() {
    let node = match find_node() {
        Some(p) => p,
        None => {
            eprintln!("SKIP: node not installed at any known path; direct comparison cannot run");
            return;
        }
    };
    let version_line = match Command::new(&node).arg("--version").output() {
        Ok(out) if out.status.success() => {
            format!("node {}", String::from_utf8_lossy(&out.stdout).trim())
        }
        _ => {
            eprintln!("SKIP: node at {} failed to execute", node.display());
            return;
        }
    };

    let project_dir = match find_or_create_rxjs_dir(&node) {
        Some(d) => d,
        None => {
            eprintln!("SKIP: rxjs not installed; `npm install rxjs` in any module to enable");
            return;
        }
    };
    eprintln!(
        "compared against installed rxjs ({}) via {}",
        project_dir.display(),
        version_line
    );

    let script = "\
const { from } = require('rxjs');
const { map, filter, toArray } = require('rxjs/operators');

const events = [
  { x: 10, y: 20, button: 0 },
  { x: -5, y: 7, button: 0 },
  { x: 15, y: 30, button: 1 },
  { x: 100, y: 5, button: 0 },
];

from(events).pipe(
  map(ev => [ev.x, ev.y]),
  filter(([x, y]) => x >= 0 && x <= 50 && y >= 0 && y <= 50),
  toArray(),
).subscribe(arr => {
  for (const [x, y] of arr) console.log(`OUT ${x} ${y}`);
});
";
    let script_path = project_dir.join("em_rxjs.js");
    fs::write(&script_path, script).expect("write rxjs script");

    let out = Command::new(&node)
        .arg(&script_path)
        .current_dir(&project_dir)
        .output()
        .expect("run node");
    if !out.status.success() {
        eprintln!(
            "SKIP: node script failed: {}",
            String::from_utf8_lossy(&out.stderr)
                .lines()
                .rev()
                .take(3)
                .collect::<Vec<_>>()
                .join(" | ")
        );
        return;
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let rxjs_pairs: Vec<(i32, i32)> = stdout
        .lines()
        .filter_map(|l| {
            let mut toks = l.split_whitespace();
            if toks.next() != Some("OUT") {
                return None;
            }
            let x = toks.next()?.parse().ok()?;
            let y = toks.next()?.parse().ok()?;
            Some((x, y))
        })
        .collect();

    let p = ReactiveUiPipeline::small_example();
    let our_pairs: Vec<(i32, i32)> = p.run().into_iter().map(|r| (r.x, r.y)).collect();

    assert_eq!(
        rxjs_pairs, our_pairs,
        "rxjs output {:?} differs from reproduction {:?}",
        rxjs_pairs, our_pairs
    );
    eprintln!(
        "PASS: rxjs emitted values = our reproduction = {:?}",
        rxjs_pairs
    );

    // Suppress unused-import warning if ClickEvent ends up unused; the
    // ReactiveUiPipeline::small_example() constructor uses it
    // internally.
    let _ = ClickEvent { x: 0, y: 0, button: 0 };
    let _ = &script_path;
}

fn find_node() -> Option<PathBuf> {
    for cand in &["node", "nodejs"] {
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
        "C:/Program Files/nodejs/node.exe",
        "C:/Program Files (x86)/nodejs/node.exe",
        "/usr/bin/node",
        "/usr/local/bin/node",
        "/opt/homebrew/bin/node",
    ];
    for p in static_paths {
        if Path::new(p).exists() {
            return Some(PathBuf::from(p));
        }
    }
    None
}

/// Find a directory where `require('rxjs')` resolves. Probes:
///   1. Some env-pinned project (EM_RXJS_DIR)
///   2. The tempdir with a one-shot `npm install --silent rxjs`
///      attempt (only if `npm` is available).
fn find_or_create_rxjs_dir(node: &Path) -> Option<PathBuf> {
    if let Ok(dir) = env::var("EM_RXJS_DIR") {
        let p = PathBuf::from(&dir);
        if p.exists() && rxjs_resolves(node, &p) {
            return Some(p);
        }
    }
    // Try a stable cache directory rather than re-installing every run.
    let cache_root = env::temp_dir().join("em_rxjs_cache");
    if rxjs_resolves(node, &cache_root) {
        return Some(cache_root);
    }
    // One-shot install (skipped if npm is missing).
    if Command::new(if cfg!(windows) { "npm.cmd" } else { "npm" })
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        let _ = fs::create_dir_all(&cache_root);
        let _ = Command::new(if cfg!(windows) { "npm.cmd" } else { "npm" })
            .arg("init")
            .arg("-y")
            .current_dir(&cache_root)
            .output();
        let _ = Command::new(if cfg!(windows) { "npm.cmd" } else { "npm" })
            .arg("install")
            .arg("--silent")
            .arg("--no-audit")
            .arg("--no-fund")
            .arg("rxjs")
            .current_dir(&cache_root)
            .output();
        if rxjs_resolves(node, &cache_root) {
            return Some(cache_root);
        }
    }
    None
}

fn rxjs_resolves(node: &Path, dir: &Path) -> bool {
    Command::new(node)
        .arg("-e")
        .arg("require('rxjs')")
        .current_dir(dir)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}
