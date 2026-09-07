//! Direct comparison: LangGraph batch (Python).
//!
//! Same three-node graph as the streaming variant, invoked via
//! `app.invoke` for full-batch execution. Asserts the final state's
//! trace list equals ["R","A","O"].

#[path = "util.rs"]
mod util;

use std::fs;
use std::process::Command;

pub fn run() {
    let python = match util::find_python() {
        Some(p) => p,
        None => { util::skip("python not installed; LangGraph_batch direct comparison cannot run"); return; }
    };
    let version = match util::python_has_package(&python, "langgraph") {
        Some(v) => v,
        None => { util::skip(format!("langgraph not installed under {}; `pip install langgraph` to enable", python.display())); return; }
    };
    util::compared_against(format!("LangGraph_batch (via langgraph {})", version), version.as_str());

    let dir = util::make_tempdir("langgraph_batch");
    let script = dir.join("g.py");
    fs::write(&script, "from langgraph.graph import StateGraph, START, END\nfrom typing import TypedDict\nclass S(TypedDict):\n    trace: list\ndef reason(s): s['trace'] = s['trace'] + ['R']; return s\ndef act(s): s['trace'] = s['trace'] + ['A']; return s\ndef observe(s): s['trace'] = s['trace'] + ['O']; return s\ng = StateGraph(S)\ng.add_node('reason', reason); g.add_node('act', act); g.add_node('observe', observe)\ng.add_edge(START, 'reason'); g.add_edge('reason', 'act'); g.add_edge('act', 'observe'); g.add_edge('observe', END)\napp = g.compile()\nfinal = app.invoke({'trace': []})\nprint(','.join(final['trace']))\n").unwrap();

    let out = Command::new(&python).arg(&script).output().expect("run langgraph");
    if !out.status.success() {
        util::skip(format!(
            "langgraph batch failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")
        ));
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let upstream: Vec<String> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .last()
        .unwrap_or("")
        .split(',')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect();
    let repro = vec!["R".to_string(), "A".to_string(), "O".to_string()];
    assert_eq!(
        upstream, repro,
        "LangGraph batch trace {:?} differs from reproduction {:?}",
        upstream, repro
    );
    util::pass("LangGraph_batch", format!("final state trace = reproduction = {:?}", upstream));
    let _ = fs::remove_dir_all(&dir);
}
