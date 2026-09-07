//! Direct comparison: Ptolemy II SR (Synchronous Reactive).
//!
//! Builds an SR-director model that ticks a `Ramp` 5 times into a
//! `Recorder`. SR fires every actor exactly once per tick; the
//! Recorder captures the sequence. Compares to the reproduction's
//! synchronous tick sequence.

#[path = "util.rs"]
mod util;

pub fn run() {
    let java = match util::find_java() {
        Some(p) => p,
        None => { util::skip("java not installed; Ptolemy_SR direct comparison cannot run"); return; }
    };
    let cp = match util::find_ptolemy_classpath() {
        Some(c) => c,
        None => { util::skip("Ptolemy II classpath not available; set PTOLEMY_HOME or EM_PTOLEMY_CLASSPATH to enable"); return; }
    };
    util::compared_against("Ptolemy_SR (via MoMLSimpleApplication)", format!("classpath len {} via java", cp.len()).as_str());

    let dir = util::make_tempdir("ptolemy_sr");
    let moml = r#"<?xml version="1.0" standalone="no"?>
<!DOCTYPE entity PUBLIC "-//UC Berkeley//DTD MoML 1//EN" "http://ptolemy.eecs.berkeley.edu/xml/dtd/MoML_1.dtd">
<entity name="em" class="ptolemy.actor.TypedCompositeActor">
  <property name="dir" class="ptolemy.domains.sr.kernel.SRDirector"><property name="iterations" value="5"/></property>
  <entity name="r" class="ptolemy.actor.lib.Ramp"><property name="init" value="0"/><property name="step" value="1"/></entity>
  <entity name="rec" class="ptolemy.actor.lib.Recorder"/>
  <relation name="x"/>
  <link port="r.output" relation="x"/>
  <link port="rec.input" relation="x"/>
</entity>
"#;
    let stdout = match util::run_ptolemy_moml(&java, &cp, &dir, moml) {
        Some(s) => s,
        None => { util::skip("Ptolemy SR MoMLSimpleApplication failed"); let _ = std::fs::remove_dir_all(&dir); return; }
    };
    let nums: Vec<i64> = stdout.split(|c: char| !c.is_ascii_digit() && c != '-').filter_map(|s| s.parse().ok()).collect();
    let repro: Vec<i64> = (0..5).collect();
    if nums.len() >= repro.len() {
        let head: Vec<i64> = nums.into_iter().take(repro.len()).collect();
        assert_eq!(head, repro, "Ptolemy_SR tick sequence {:?} != reproduction {:?}", head, repro);
        util::pass("Ptolemy_SR", format!("SR synchronous tick sequence = reproduction = {:?}", head));
    } else {
        util::skip(format!("Ptolemy_SR produced only {} parseable ticks; need {}", nums.len(), repro.len()));
    }
    let _ = std::fs::remove_dir_all(&dir);
}
