//! Shared utilities for direct_comparison harnesses.
//!
//! Common patterns: detect a binary, a Python package, a Node module,
//! or a JVM tool by searching PATH and a curated list of full paths;
//! print a SKIP line if absent; print a PASS line with the upstream
//! version if present.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Find a binary by name on PATH or in a static list of full paths.
/// Always also probes chocolatey's shim dir, Git Bash's bin dirs,
/// MSYS2's usr/bin, common Program Files install locations, and Unix
/// system bin dirs. This makes the harness detect installed tools
/// regardless of whether the user has shellrc-tweaked their PATH.
pub fn find_binary(name: &str, static_paths: &[&str]) -> Option<PathBuf> {
    if Command::new(name)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        return Some(PathBuf::from(name));
    }
    // Caller-supplied static paths take precedence.
    for p in static_paths {
        if Path::new(p).exists() {
            return Some(PathBuf::from(p));
        }
    }
    // Default fallback: probe well-known Windows + Unix install dirs
    // for `<name>.exe` and `<name>`.
    let exts = if cfg!(windows) { &[".exe", ""][..] } else { &[""][..] };
    let dirs = [
        // chocolatey shim dir (most choco-installed tools land here)
        "C:/ProgramData/chocolatey/bin",
        // Git Bash bundles bash + make + many Unix tools
        "C:/Program Files/Git/bin",
        "C:/Program Files/Git/usr/bin",
        "C:/Program Files/Git/mingw64/bin",
        // MSYS2
        "C:/msys64/usr/bin",
        // Common per-tool install dirs (best-effort)
        "C:/Program Files/nodejs",
        "C:/Program Files/dotnet",
        "C:/Program Files (x86)/Microsoft SDKs/MPI/Bin",
        "C:/Program Files/Microsoft MPI/Bin",
        // Unix system dirs
        "/usr/bin",
        "/usr/local/bin",
        "/opt/homebrew/bin",
        "/bin",
    ];
    for dir in &dirs {
        for ext in exts {
            let candidate = PathBuf::from(format!("{}/{}{}", dir, name, ext));
            if candidate.exists() {
                return Some(candidate);
            }
        }
    }
    None
}

/// Standard Python discovery (Windows + Unix).
pub fn find_python() -> Option<PathBuf> {
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
    if let Ok(local) = env::var("LOCALAPPDATA") {
        let root = PathBuf::from(&local).join("Programs").join("Python");
        if let Ok(entries) = fs::read_dir(&root) {
            for entry in entries.flatten() {
                let exe = entry.path().join("python.exe");
                if exe.exists() {
                    return Some(exe);
                }
            }
        }
    }
    for cand in &[
        "/usr/bin/python3",
        "/usr/local/bin/python3",
        "/opt/homebrew/bin/python3",
    ] {
        let p = Path::new(cand);
        if p.exists() {
            return Some(p.to_path_buf());
        }
    }
    None
}

/// Standard Node.js discovery.
pub fn find_node() -> Option<PathBuf> {
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

/// Probe whether a Python package is importable.
pub fn python_has_package(python: &Path, package: &str) -> Option<String> {
    let code = format!("import {0}; print(getattr({0}, '__version__', 'installed'))", package);
    let out = Command::new(python).arg("-c").arg(code).output().ok()?;
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

/// Probe whether a Node package is resolvable from a directory.
pub fn node_has_package(node: &Path, pkg: &str, dir: &Path) -> Option<String> {
    let code = format!("const p=require('{}'); console.log(require('{}/package.json').version);", pkg, pkg);
    let out = Command::new(node)
        .arg("-e")
        .arg(code)
        .current_dir(dir)
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

/// One-shot npm install of a package into a stable cache directory,
/// then probe for resolvability. Returns the cache directory on
/// success.
pub fn ensure_node_package(node: &Path, pkg: &str) -> Option<PathBuf> {
    if let Ok(dir) = env::var(format!("EM_{}_DIR", pkg.to_uppercase().replace('-', "_"))) {
        let p = PathBuf::from(&dir);
        if p.exists() && node_has_package(node, pkg, &p).is_some() {
            return Some(p);
        }
    }
    let cache = env::temp_dir().join(format!("em_node_{}_cache", pkg.replace('/', "_").replace('@', "")));
    if node_has_package(node, pkg, &cache).is_some() {
        return Some(cache);
    }
    let npm = if cfg!(windows) { "npm.cmd" } else { "npm" };
    if Command::new(npm)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        let _ = fs::create_dir_all(&cache);
        let _ = Command::new(npm)
            .arg("init")
            .arg("-y")
            .current_dir(&cache)
            .output();
        let _ = Command::new(npm)
            .arg("install")
            .arg("--silent")
            .arg("--no-audit")
            .arg("--no-fund")
            .arg(pkg)
            .current_dir(&cache)
            .output();
        if node_has_package(node, pkg, &cache).is_some() {
            return Some(cache);
        }
    }
    None
}

/// Compose a tempdir for a per-test workspace.
pub fn make_tempdir(prefix: &str) -> PathBuf {
    let dir = env::temp_dir().join(format!(
        "em_{}_{}_{}",
        prefix,
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    fs::create_dir_all(&dir).expect("create tempdir");
    dir
}

/// Locate `jshell` (ships with every modern JDK). Probes PATH and
/// the well-known Windows JDK install dirs.
pub fn find_jshell() -> Option<PathBuf> {
    if Command::new("jshell")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        return Some(PathBuf::from("jshell"));
    }
    let mut candidates: Vec<PathBuf> = Vec::new();
    for base in &[
        "C:/Program Files/Java",
        "C:/Program Files/Microsoft",
        "C:/Program Files/Eclipse Adoptium",
        "C:/Program Files (x86)/Java",
    ] {
        if let Ok(entries) = fs::read_dir(base) {
            for entry in entries.flatten() {
                candidates.push(entry.path().join("bin").join("jshell.exe"));
            }
        }
    }
    if let Ok(local) = env::var("LOCALAPPDATA") {
        let pkgs = PathBuf::from(local).join("Microsoft").join("WinGet").join("Packages");
        if let Ok(entries) = fs::read_dir(&pkgs) {
            for entry in entries.flatten() {
                if let Ok(inner) = fs::read_dir(entry.path()) {
                    for sub in inner.flatten() {
                        candidates.push(sub.path().join("bin").join("jshell.exe"));
                    }
                }
            }
        }
    }
    for p in candidates {
        if p.exists() {
            return Some(p);
        }
    }
    None
}

/// Resolve a JVM classpath for given Maven coordinates using coursier
/// (`cs fetch --classpath <coords...>`). Returns the colon/semicolon-
/// delimited classpath string on success.
pub fn resolve_via_coursier(coords: &[&str]) -> Option<String> {
    for cs in &["cs", "coursier"] {
        if Command::new(cs)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            let mut cmd = Command::new(cs);
            cmd.arg("fetch").arg("--classpath");
            for c in coords {
                cmd.arg(c);
            }
            if let Ok(out) = cmd.output() {
                if out.status.success() {
                    let cp = String::from_utf8_lossy(&out.stdout).trim().to_string();
                    if !cp.is_empty() {
                        return Some(cp);
                    }
                }
            }
        }
    }
    None
}

/// Read a classpath either from `env_var` (set by the user) or via
/// coursier with `coords`. Returns the classpath string and a short
/// human-readable provenance ("env=$VAR" or "coursier=$first_coord").
pub fn jvm_classpath(env_var: &str, coords: &[&str]) -> Option<(String, String)> {
    if let Ok(cp) = env::var(env_var) {
        if !cp.is_empty() {
            return Some((cp, format!("env={}", env_var)));
        }
    }
    if let Some(cp) = resolve_via_coursier(coords) {
        return Some((cp, format!("coursier={}", coords.first().copied().unwrap_or(""))));
    }
    None
}

/// Run a jshell driver with a given classpath and return its stdout
/// (or None if the run failed).
pub fn run_jshell(jshell: &Path, classpath: &str, prefix: &str, source: &str) -> Option<String> {
    let script = env::temp_dir().join(format!(
        "em_{}_{}_{}.jsh",
        prefix,
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    fs::write(&script, source).ok()?;
    let out = Command::new(jshell)
        .arg("--class-path")
        .arg(classpath)
        .arg(&script)
        .output()
        .ok()?;
    let _ = fs::remove_file(&script);
    if !out.status.success() {
        let tail = String::from_utf8_lossy(&out.stderr)
            .lines()
            .rev()
            .take(5)
            .collect::<Vec<_>>()
            .join(" | ");
        eprintln!("jshell driver failed: stderr tail = {}", tail);
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// Locate `java` (any JDK or JRE 8+). Probes PATH and well-known
/// Windows JDK install dirs.
pub fn find_java() -> Option<PathBuf> {
    if Command::new("java")
        .arg("-version")
        .output()
        .map(|o| o.status.success() || !o.stderr.is_empty())
        .unwrap_or(false)
    {
        return Some(PathBuf::from("java"));
    }
    for base in &[
        "C:/Program Files/Java",
        "C:/Program Files/Microsoft",
        "C:/Program Files/Eclipse Adoptium",
        "C:/Program Files (x86)/Java",
    ] {
        if let Ok(entries) = fs::read_dir(base) {
            for entry in entries.flatten() {
                let p = entry.path().join("bin").join("java.exe");
                if p.exists() {
                    return Some(p);
                }
            }
        }
    }
    None
}

/// Locate the Ptolemy II classpath. Looks for `EM_PTOLEMY_CLASSPATH`
/// first; failing that, looks for `PTOLEMY_HOME` and builds the
/// canonical classpath from its `ptolemy/lib` and `lib` directories.
pub fn find_ptolemy_classpath() -> Option<String> {
    if let Ok(cp) = env::var("EM_PTOLEMY_CLASSPATH") {
        if !cp.is_empty() {
            return Some(cp);
        }
    }
    if let Ok(home) = env::var("PTOLEMY_HOME") {
        let home_p = PathBuf::from(&home);
        if !home_p.exists() {
            return None;
        }
        let sep = if cfg!(windows) { ";" } else { ":" };
        let mut parts: Vec<String> = vec![home.clone()];
        for sub in &["ptolemy", "ptolemy/lib", "lib"] {
            let d = home_p.join(sub);
            if let Ok(entries) = fs::read_dir(&d) {
                for entry in entries.flatten() {
                    if entry.path().extension().map(|e| e == "jar").unwrap_or(false) {
                        parts.push(entry.path().to_string_lossy().into_owned());
                    }
                }
            }
        }
        if parts.len() > 1 {
            return Some(parts.join(sep));
        }
    }
    None
}

/// Run a Ptolemy II MoML model headlessly via `MoMLSimpleApplication`,
/// returning stdout on success. Writes `moml` into a temp .xml file
/// inside `dir`.
pub fn run_ptolemy_moml(java: &Path, classpath: &str, dir: &Path, moml: &str) -> Option<String> {
    let model = dir.join("model.xml");
    fs::write(&model, moml).ok()?;
    let out = Command::new(java)
        .arg("-classpath")
        .arg(classpath)
        .arg("ptolemy.moml.MoMLSimpleApplication")
        .arg(&model)
        .current_dir(dir)
        .output()
        .ok()?;
    if !out.status.success() {
        let tail = String::from_utf8_lossy(&out.stderr)
            .lines()
            .rev()
            .take(5)
            .collect::<Vec<_>>()
            .join(" | ");
        eprintln!("Ptolemy MoMLSimpleApplication failed: stderr tail = {}", tail);
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// Standard SKIP printer. Accepts anything string-like.
pub fn skip(reason: impl AsRef<str>) {
    eprintln!("SKIP: {}", reason.as_ref());
}

/// Standard "compared against" printer.
pub fn compared_against(framework: impl AsRef<str>, version: impl AsRef<str>) {
    eprintln!(
        "compared against installed {}: {}",
        framework.as_ref(),
        version.as_ref()
    );
}

/// Standard PASS printer.
pub fn pass(framework: impl AsRef<str>, detail: impl AsRef<str>) {
    eprintln!("PASS: {} {}", framework.as_ref(), detail.as_ref());
}
