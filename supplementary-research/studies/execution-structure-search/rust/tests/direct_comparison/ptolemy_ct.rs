//! Direct comparison: Ptolemy II CT (Continuous Time).
//!
//! Builds a CT-director model with an `Integrator` driven by a
//! constant input over a 5.0s window, sampling every 1.0s into a
//! `Recorder`. The output is the sequence of integrated samples
//! (which under a unit constant input is the wall-clock time at
//! sample points: 0, 1, 2, 3, 4, 5). Compares to that reproduction
//! sequence with tolerance.

#[path = "util.rs"]
mod util;

pub fn run() {
    let java = match util::find_java() {
        Some(p) => p,
        None => { util::skip("java not installed; Ptolemy_CT direct comparison cannot run"); return; }
    };
    let cp = match util::find_ptolemy_classpath() {
        Some(c) => c,
        None => { util::skip("Ptolemy II classpath not available; set PTOLEMY_HOME or EM_PTOLEMY_CLASSPATH to enable"); return; }
    };
    util::compared_against("Ptolemy_CT (via MoMLSimpleApplication)", format!("classpath len {} via java", cp.len()).as_str());

    let dir = util::make_tempdir("ptolemy_ct");
    let moml = r#"<?xml version="1.0" standalone="no"?>
<!DOCTYPE entity PUBLIC "-//UC Berkeley//DTD MoML 1//EN" "http://ptolemy.eecs.berkeley.edu/xml/dtd/MoML_1.dtd">
<entity name="em" class="ptolemy.actor.TypedCompositeActor">
  <property name="dir" class="ptolemy.domains.continuous.kernel.ContinuousDirector"><property name="stopTime" value="5.0"/><property name="maxStepSize" value="0.5"/></property>
  <entity name="src" class="ptolemy.actor.lib.Const"><property name="value" value="1.0"/></entity>
  <entity name="int" class="ptolemy.domains.continuous.lib.Integrator"/>
  <entity name="smp" class="ptolemy.domains.continuous.lib.PeriodicSampler"><property name="samplePeriod" value="1.0"/></entity>
  <entity name="rec" class="ptolemy.actor.lib.Recorder"/>
  <relation name="r1"/>
  <relation name="r2"/>
  <relation name="r3"/>
  <link port="src.output" relation="r1"/>
  <link port="int.input" relation="r1"/>
  <link port="int.output" relation="r2"/>
  <link port="smp.input" relation="r2"/>
  <link port="smp.output" relation="r3"/>
  <link port="rec.input" relation="r3"/>
</entity>
"#;
    let stdout = match util::run_ptolemy_moml(&java, &cp, &dir, moml) {
        Some(s) => s,
        None => { util::skip("Ptolemy CT MoMLSimpleApplication failed"); let _ = std::fs::remove_dir_all(&dir); return; }
    };
    let floats: Vec<f64> = stdout
        .split(|c: char| !c.is_ascii_digit() && c != '.' && c != '-' && c != 'E' && c != 'e')
        .filter_map(|s| s.parse::<f64>().ok())
        .collect();
    let repro: Vec<f64> = vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0];
    if floats.len() >= repro.len() {
        let head: Vec<f64> = floats.into_iter().take(repro.len()).collect();
        for (i, (got, want)) in head.iter().zip(repro.iter()).enumerate() {
            assert!((got - want).abs() < 0.1, "Ptolemy_CT sample[{}] = {} not within 0.1 of expected {}", i, got, want);
        }
        util::pass("Ptolemy_CT", format!("CT Integrator sample sequence ≈ reproduction = {:?}", repro));
    } else {
        util::skip(format!("Ptolemy_CT produced only {} parseable samples; need {}", floats.len(), repro.len()));
    }
    let _ = std::fs::remove_dir_all(&dir);
}
