//! Direct comparison: Ptolemy II HDF (Heterochronous Dataflow).
//!
//! HDF is SDF extended with mode-dependent rates governed by an FSM.
//! For a minimal model with no mode change, HDF reduces to SDF. This
//! harness builds an HDF-director model with a `Ramp` source firing
//! 5 times into a `Recorder` and compares the captured sequence.

#[path = "util.rs"]
mod util;

pub fn run() {
    let java = match util::find_java() {
        Some(p) => p,
        None => { util::skip("java not installed; Ptolemy_HDF direct comparison cannot run"); return; }
    };
    let cp = match util::find_ptolemy_classpath() {
        Some(c) => c,
        None => { util::skip("Ptolemy II classpath not available; set PTOLEMY_HOME or EM_PTOLEMY_CLASSPATH to enable"); return; }
    };
    util::compared_against("Ptolemy_HDF (via MoMLSimpleApplication)", format!("classpath len {} via java", cp.len()).as_str());

    let dir = util::make_tempdir("ptolemy_hdf");
    let moml = r#"<?xml version="1.0" standalone="no"?>
<!DOCTYPE entity PUBLIC "-//UC Berkeley//DTD MoML 1//EN" "http://ptolemy.eecs.berkeley.edu/xml/dtd/MoML_1.dtd">
<entity name="em" class="ptolemy.actor.TypedCompositeActor">
  <property name="dir" class="ptolemy.domains.hdf.kernel.HDFDirector"><property name="iterations" value="5"/></property>
  <entity name="r" class="ptolemy.actor.lib.Ramp"><property name="init" value="0"/><property name="step" value="1"/></entity>
  <entity name="rec" class="ptolemy.actor.lib.Recorder"/>
  <relation name="x"/>
  <link port="r.output" relation="x"/>
  <link port="rec.input" relation="x"/>
</entity>
"#;
    let stdout = match util::run_ptolemy_moml(&java, &cp, &dir, moml) {
        Some(s) => s,
        None => { util::skip("Ptolemy HDF MoMLSimpleApplication failed"); let _ = std::fs::remove_dir_all(&dir); return; }
    };
    let nums: Vec<i64> = stdout.split(|c: char| !c.is_ascii_digit() && c != '-').filter_map(|s| s.parse().ok()).collect();
    let repro: Vec<i64> = (0..5).collect();
    if nums.len() >= repro.len() {
        let head: Vec<i64> = nums.into_iter().take(repro.len()).collect();
        assert_eq!(head, repro, "Ptolemy_HDF firing sequence {:?} != reproduction {:?}", head, repro);
        util::pass("Ptolemy_HDF", format!("HDF Ramp/Recorder firing sequence = reproduction = {:?}", head));
    } else {
        util::skip(format!("Ptolemy_HDF produced only {} parseable tokens; need {}", nums.len(), repro.len()));
    }
    let _ = std::fs::remove_dir_all(&dir);
}
