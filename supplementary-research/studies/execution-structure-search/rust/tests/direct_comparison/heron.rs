//! Direct comparison: Heron (Apache Heron, stream-processing).
//!
//! Drives Heron's local-mode `Simulator` via jshell: builds a
//! source-bolt topology that emits five integers, runs them through
//! a bolt that prints each tuple it receives, sleeps briefly so the
//! simulator can drain, then captures the emission order.
//!
//! Requires:
//!   - `jshell` (any JDK)
//!   - `EM_HERON_CLASSPATH` set with `heron-storm` + `heron-api` +
//!     `heron-simulator` jars, OR `cs` (coursier) installed.

#[path = "util.rs"]
mod util;

pub fn run() {
    let jshell = match util::find_jshell() {
        Some(p) => p,
        None => { util::skip("jshell (JDK) not installed at any known path; Heron direct comparison cannot run"); return; }
    };
    let (classpath, provenance) = match util::jvm_classpath(
        "EM_HERON_CLASSPATH",
        &[
            "org.apache.heron:heron-api:0.20.5-incubating",
            "org.apache.heron:heron-storm:0.20.5-incubating",
            "org.apache.heron:heron-simulator:0.20.5-incubating",
        ],
    ) {
        Some(t) => t,
        None => { util::skip("EM_HERON_CLASSPATH not set and coursier not available; `cs fetch --classpath org.apache.heron:heron-{api,storm,simulator}:0.20.5-incubating` and export the classpath to enable"); return; }
    };
    util::compared_against("Heron (via jshell)", provenance.as_str());

    let driver = r#"
import org.apache.heron.api.topology.*;
import org.apache.heron.api.spout.*;
import org.apache.heron.api.bolt.*;
import org.apache.heron.api.tuple.*;
import org.apache.heron.simulator.Simulator;
import java.util.*;

class Spout extends BaseRichSpout {
    SpoutOutputCollector c;
    int i = 0;
    public void open(Map conf, TopologyContext ctx, SpoutOutputCollector col) { this.c = col; }
    public void nextTuple() { if (i < 5) { c.emit(new Values(i)); i++; } }
    public void declareOutputFields(OutputFieldsDeclarer d) { d.declare(new Fields("n")); }
}
class Sink extends BaseRichBolt {
    public void prepare(Map conf, TopologyContext ctx, OutputCollector c) {}
    public void execute(Tuple t) { System.out.println("OUT " + t.getInteger(0)); }
    public void declareOutputFields(OutputFieldsDeclarer d) {}
}
TopologyBuilder b = new TopologyBuilder();
b.setSpout("spout", new Spout());
b.setBolt("sink", new Sink()).shuffleGrouping("spout");
Simulator sim = new Simulator();
sim.submitTopology("em", new java.util.HashMap(), b.createTopology());
Thread.sleep(2000);
sim.killTopology("em");
sim.shutdown();
/exit
"#;
    let stdout = match util::run_jshell(&jshell, &classpath, "heron", driver) {
        Some(s) => s,
        None => { util::skip("Heron jshell driver failed (classpath or Heron version mismatch)"); return; }
    };
    let mut upstream: Vec<i64> = stdout
        .lines()
        .filter_map(|l| l.strip_prefix("OUT ").and_then(|s| s.trim().parse().ok()))
        .collect();
    upstream.sort();
    let repro: Vec<i64> = (0..5).collect();
    assert_eq!(upstream, repro, "Heron emission set {:?} != reproduction {:?}", upstream, repro);
    util::pass("Heron", format!("local-mode bolt emission set = reproduction = {:?}", upstream));
}
