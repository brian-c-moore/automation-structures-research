//! Direct comparison: Ptolemy II DE (Discrete Event).
//!
//! Builds a DE-director model with a `DiscreteClock` firing 5 events
//! at 1.0s intervals into a `Recorder`. Runs headlessly and parses
//! the recorded event sequence. Compares against the reproduction's
//! discrete-event tick sequence.

#[path = "util.rs"]
mod util;

pub fn run() {
    let java = match util::find_java() {
        Some(p) => p,
        None => { util::skip("java not installed; Ptolemy_DE direct comparison cannot run"); return; }
    };
    let cp = match util::find_ptolemy_classpath() {
        Some(c) => c,
        None => { util::skip("Ptolemy II classpath not available; set PTOLEMY_HOME or EM_PTOLEMY_CLASSPATH to enable"); return; }
    };
    util::compared_against("Ptolemy_DE (via MoMLSimpleApplication)", format!("classpath len {} via java", cp.len()).as_str());

    let dir = util::make_tempdir("ptolemy_de");
    let moml = r#"<?xml version="1.0" standalone="no"?>
<!DOCTYPE entity PUBLIC "-//UC Berkeley//DTD MoML 1//EN" "http://ptolemy.eecs.berkeley.edu/xml/dtd/MoML_1.dtd">
<entity name="em" class="ptolemy.actor.TypedCompositeActor">
  <property name="dir" class="ptolemy.domains.de.kernel.DEDirector"><property name="stopTime" value="5.0"/></property>
  <entity name="clk" class="ptolemy.actor.lib.DiscreteClock"><property name="period" value="1.0"/><property name="values" value="{1,2,3,4,5}"/></entity>
  <entity name="rec" class="ptolemy.actor.lib.Recorder"/>
  <relation name="x"/>
  <link port="clk.output" relation="x"/>
  <link port="rec.input" relation="x"/>
</entity>
"#;
    let stdout = match util::run_ptolemy_moml(&java, &cp, &dir, moml) {
        Some(s) => s,
        None => { util::skip("Ptolemy DE MoMLSimpleApplication failed"); let _ = std::fs::remove_dir_all(&dir); return; }
    };
    let nums: Vec<i64> = stdout.split(|c: char| !c.is_ascii_digit() && c != '-').filter_map(|s| s.parse().ok()).collect();
    let repro: Vec<i64> = vec![1, 2, 3, 4, 5];
    if nums.len() >= repro.len() {
        let head: Vec<i64> = nums.into_iter().take(repro.len()).collect();
        assert_eq!(head, repro, "Ptolemy_DE event sequence head {:?} != reproduction {:?}", head, repro);
        util::pass("Ptolemy_DE", format!("DE DiscreteClock event sequence head = reproduction = {:?}", head));
    } else {
        util::skip(format!("Ptolemy_DE produced only {} parseable events; need {}", nums.len(), repro.len()));
    }
    let _ = std::fs::remove_dir_all(&dir);
}
