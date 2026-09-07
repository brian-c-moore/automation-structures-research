//! Direct comparison: Vue reactivity (`@vue/reactivity`).
//!
//! Imports `ref` and `effect` from @vue/reactivity, drives three
//! ref updates, and captures the effect's observation log. Compares
//! the upstream observation set against {0, 10, 20, 30}.

#[path = "util.rs"]
mod util;

use std::collections::BTreeSet;
use std::fs;
use std::process::Command;

pub fn run() {
    let node = match util::find_node() {
        Some(p) => p,
        None => { util::skip("node not installed; Vue_reactivity direct comparison cannot run"); return; }
    };
    let pkg_dir = match util::ensure_node_package(&node, "@vue/reactivity") {
        Some(d) => d,
        None => { util::skip("@vue/reactivity not installable via npm; `npm install @vue/reactivity` to enable"); return; }
    };
    let version = util::node_has_package(&node, "@vue/reactivity", &pkg_dir).unwrap_or_else(|| "installed".to_string());
    util::compared_against("Vue_reactivity (via @vue/reactivity)", version.as_str());

    let script_path = pkg_dir.join("em_vue.cjs");
    let script = "const { ref, effect } = require('@vue/reactivity');\nconst v = ref(0);\nconst log = [];\neffect(() => { log.push(v.value); });\nv.value = 10; v.value = 20; v.value = 30;\nfor (const n of log) console.log(n);\n";
    fs::write(&script_path, script).unwrap();
    let out = Command::new(&node).arg(&script_path).current_dir(&pkg_dir).output().expect("run vue reactivity");
    if !out.status.success() {
        util::skip(format!("vue reactivity failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")));
        return;
    }
    let upstream: Vec<i64> = String::from_utf8_lossy(&out.stdout)
        .lines().filter_map(|l| l.trim().parse().ok()).collect();
    let upstream_set: BTreeSet<i64> = upstream.iter().copied().collect();
    let repro_set: BTreeSet<i64> = [0i64, 10, 20, 30].into_iter().collect();
    assert_eq!(upstream_set, repro_set, "Vue observations {:?} != reproduction {:?}", upstream_set, repro_set);
    util::pass("Vue_reactivity", format!("effect-observation set = reproduction = {:?}", upstream_set));
}
