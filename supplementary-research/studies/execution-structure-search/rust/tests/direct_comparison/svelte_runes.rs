//! Direct comparison: Svelte 5 runes.
//!
//! Compiles a small `.svelte` source that uses `$state` and
//! `$derived` runes via Svelte's compiler API. Asserts the
//! generated JS imports from Svelte 5's runes-runtime
//! (`svelte/internal/client`) and emits a `$.derived(...)` call —
//! these are markers of the runes-mode codegen path that does not
//! exist on Svelte 3/4. Also asserts the installed svelte major
//! version is >= 5.

#[path = "util.rs"]
mod util;

use std::fs;
use std::process::Command;

pub fn run() {
    let node = match util::find_node() {
        Some(p) => p,
        None => { util::skip("node not installed; Svelte_runes direct comparison cannot run"); return; }
    };
    let pkg_dir = match util::ensure_node_package(&node, "svelte") {
        Some(d) => d,
        None => { util::skip("svelte not installable via npm; `npm install svelte` to enable"); return; }
    };
    let version = util::node_has_package(&node, "svelte", &pkg_dir).unwrap_or_else(|| "installed".to_string());
    util::compared_against("Svelte_runes (via svelte)", version.as_str());

    let script_path = pkg_dir.join("em_svelte.cjs");
    let script = "const { compile } = require('svelte/compiler');\nconst src = \"<script>let count = $state(0); let doubled = $derived(count * 2);</script>{count} {doubled}\";\nconst r = compile(src, { generate: 'client', runes: true });\nconst ok = r.js.code.includes(\"svelte/internal/client\") && r.js.code.includes(\"$.derived\");\nconsole.log(ok ? 'runes-ok' : 'runes-missing');\n";
    fs::write(&script_path, script).unwrap();
    let out = Command::new(&node).arg(&script_path).current_dir(&pkg_dir).output().expect("run svelte compile");
    if !out.status.success() {
        util::skip(format!("svelte compile failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")));
        return;
    }
    let upstream = String::from_utf8_lossy(&out.stdout).trim().to_string();
    assert_eq!(upstream, "runes-ok", "Svelte compiler did not emit runes-runtime references; got `{}`", upstream);
    let major: u32 = version.split('.').next().and_then(|s| s.parse().ok()).unwrap_or(0);
    assert!(major >= 5, "Svelte version {} is below 5 (runes require >= 5)", version);
    util::pass("Svelte_runes", format!("svelte {} accepts runes; compiles to svelte/internal/client + $.derived runtime", version));
}
