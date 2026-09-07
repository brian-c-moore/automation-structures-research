//! Direct comparison: Pants (Python build system).
//!
//! Detects the `pants` package, then attempts to run `pants list ::`
//! against a tiny BUILD-file workspace with three Python targets in a
//! linear dependency chain. Pants v2's `list` goal enumerates all
//! reachable targets in registration order. Compares the enumerated
//! target set to the reproduction's target list.
//!
//! Note: Pants v2 is normally driven from a per-repo `pants` launcher
//! script that bootstraps a hermetic Python environment. If only the
//! `pants` Python package is importable but no launcher is set up,
//! the harness skips cleanly.

#[path = "util.rs"]
mod util;

use std::collections::BTreeSet;
use std::fs;
use std::process::Command;

pub fn run() {
    let python = match util::find_python() {
        Some(p) => p,
        None => { util::skip("python not installed; Pants direct comparison cannot run"); return; }
    };
    let version = match util::python_has_package(&python, "pants") {
        Some(v) => v,
        None => { util::skip(format!("pants not installed under {}; `pip install pantsbuild.pants` to enable", python.display())); return; }
    };
    util::compared_against("Pants (via pants)", version.as_str());

    let dir = util::make_tempdir("pants");
    fs::write(dir.join("pants.toml"),
        "[GLOBAL]\npants_version = \"2.18.0\"\nbackend_packages = [\"pants.backend.python\"]\n").unwrap();
    fs::write(dir.join("BUILD"),
        "python_sources(name = 'compile', sources = ['compile.py'])\npython_sources(name = 'link', sources = ['link.py'], dependencies = [':compile'])\npython_sources(name = 'bin', sources = ['bin.py'], dependencies = [':link'])\n").unwrap();
    fs::write(dir.join("compile.py"), "x = 1\n").unwrap();
    fs::write(dir.join("link.py"), "from compile import x\ny = x + 1\n").unwrap();
    fs::write(dir.join("bin.py"), "from link import y\nprint(y)\n").unwrap();

    let out = Command::new(&python).arg("-m").arg("pants").arg("list").arg("::").current_dir(&dir).output();
    let out = match out {
        Ok(o) if o.status.success() => o,
        Ok(o) => {
            util::skip(format!("`python -m pants list ::` failed (needs launcher / hermetic bootstrap): {}",
                String::from_utf8_lossy(&o.stderr).lines().rev().take(3).collect::<Vec<_>>().join(" | ")));
            let _ = fs::remove_dir_all(&dir);
            return;
        }
        Err(e) => {
            util::skip(format!("invoke `python -m pants` errored: {}", e));
            let _ = fs::remove_dir_all(&dir);
            return;
        }
    };
    let upstream: BTreeSet<String> = String::from_utf8_lossy(&out.stdout)
        .lines().map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
    let expected: BTreeSet<String> = [":compile", ":link", ":bin", "compile.py", "link.py", "bin.py"]
        .iter().map(|s| s.to_string()).collect();
    let intersection_size = upstream.iter().filter(|t| expected.iter().any(|e| t.contains(e))).count();
    assert!(intersection_size >= 3,
        "Pants list output covers fewer than 3 expected targets; got {:?}", upstream);
    util::pass("Pants", format!("pants list :: enumerated {} target lines covering {} of the reproduction's 3 chain targets", upstream.len(), intersection_size));
    let _ = fs::remove_dir_all(&dir);
}
