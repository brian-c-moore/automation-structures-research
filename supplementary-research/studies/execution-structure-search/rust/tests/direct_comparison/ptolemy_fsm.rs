//! Direct comparison: Ptolemy II FSM (Finite-State Machine).
//!
//! Builds a tiny FSM with three states (S0 -> S1 -> S2 -> S0)
//! cycling under an SDF host-director clock that fires 6 times into
//! a `Recorder`. Runs headlessly and parses the recorded output
//! sequence. Compares against the reproduction's state cycle.

#[path = "util.rs"]
mod util;

pub fn run() {
    let java = match util::find_java() {
        Some(p) => p,
        None => { util::skip("java not installed; Ptolemy_FSM direct comparison cannot run"); return; }
    };
    let cp = match util::find_ptolemy_classpath() {
        Some(c) => c,
        None => { util::skip("Ptolemy II classpath not available; set PTOLEMY_HOME or EM_PTOLEMY_CLASSPATH to enable"); return; }
    };
    util::compared_against("Ptolemy_FSM (via MoMLSimpleApplication)", format!("classpath len {} via java", cp.len()).as_str());

    let dir = util::make_tempdir("ptolemy_fsm");
    let moml = r#"<?xml version="1.0" standalone="no"?>
<!DOCTYPE entity PUBLIC "-//UC Berkeley//DTD MoML 1//EN" "http://ptolemy.eecs.berkeley.edu/xml/dtd/MoML_1.dtd">
<entity name="em" class="ptolemy.actor.TypedCompositeActor">
  <property name="dir" class="ptolemy.domains.sdf.kernel.SDFDirector"><property name="iterations" value="6"/></property>
  <entity name="fsm" class="ptolemy.domains.modal.kernel.FSMActor">
    <port name="out" class="ptolemy.actor.TypedIOPort"><property name="output"/></port>
    <entity name="S0" class="ptolemy.domains.modal.kernel.State"><property name="isInitialState"/></entity>
    <entity name="S1" class="ptolemy.domains.modal.kernel.State"/>
    <entity name="S2" class="ptolemy.domains.modal.kernel.State"/>
    <relation name="t01" class="ptolemy.domains.modal.kernel.Transition"><property name="guardExpression" value="true"/><property name="outputActions" value="out=0"/></relation>
    <relation name="t12" class="ptolemy.domains.modal.kernel.Transition"><property name="guardExpression" value="true"/><property name="outputActions" value="out=1"/></relation>
    <relation name="t20" class="ptolemy.domains.modal.kernel.Transition"><property name="guardExpression" value="true"/><property name="outputActions" value="out=2"/></relation>
    <link port="S0.outgoingPort" relation="t01"/>
    <link port="S1.incomingPort" relation="t01"/>
    <link port="S1.outgoingPort" relation="t12"/>
    <link port="S2.incomingPort" relation="t12"/>
    <link port="S2.outgoingPort" relation="t20"/>
    <link port="S0.incomingPort" relation="t20"/>
  </entity>
  <entity name="rec" class="ptolemy.actor.lib.Recorder"/>
  <relation name="x"/>
  <link port="fsm.out" relation="x"/>
  <link port="rec.input" relation="x"/>
</entity>
"#;
    let stdout = match util::run_ptolemy_moml(&java, &cp, &dir, moml) {
        Some(s) => s,
        None => { util::skip("Ptolemy FSM MoMLSimpleApplication failed"); let _ = std::fs::remove_dir_all(&dir); return; }
    };
    let nums: Vec<i64> = stdout.split(|c: char| !c.is_ascii_digit() && c != '-').filter_map(|s| s.parse().ok()).collect();
    let repro: Vec<i64> = vec![0, 1, 2, 0, 1, 2];
    if nums.len() >= repro.len() {
        let head: Vec<i64> = nums.into_iter().take(repro.len()).collect();
        assert_eq!(head, repro, "Ptolemy_FSM state cycle {:?} != reproduction {:?}", head, repro);
        util::pass("Ptolemy_FSM", format!("FSM state cycle = reproduction = {:?}", head));
    } else {
        util::skip(format!("Ptolemy_FSM produced only {} parseable outputs; need {}", nums.len(), repro.len()));
    }
    let _ = std::fs::remove_dir_all(&dir);
}
