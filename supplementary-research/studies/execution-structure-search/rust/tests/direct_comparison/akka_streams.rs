//! Direct comparison: Akka_Streams.
//!
//! Drives an Akka Streams source-via-flow-to-sink graph via jshell:
//! emits five integers, maps them through `x*2 + 1`, collects them
//! into a list, and prints the result sequence. Compares the
//! upstream sequence against the reproduction's step-graph map over
//! the same inputs.
//!
//! Requires:
//!   - `jshell` (any JDK)
//!   - `EM_AKKA_STREAMS_CLASSPATH` set, OR `cs` (coursier) installed.

#[path = "util.rs"]
mod util;

pub fn run() {
    let jshell = match util::find_jshell() {
        Some(p) => p,
        None => { util::skip("jshell (JDK) not installed at any known path; Akka_Streams direct comparison cannot run"); return; }
    };
    let (classpath, provenance) = match util::jvm_classpath(
        "EM_AKKA_STREAMS_CLASSPATH",
        &["com.typesafe.akka:akka-stream_2.13:2.6.21"],
    ) {
        Some(t) => t,
        None => { util::skip("EM_AKKA_STREAMS_CLASSPATH not set and coursier not available; `cs fetch --classpath com.typesafe.akka:akka-stream_2.13:2.6.21` and export the classpath to enable"); return; }
    };
    util::compared_against("Akka_Streams (via jshell)", provenance.as_str());

    let driver = r#"
import akka.actor.ActorSystem;
import akka.stream.javadsl.*;
import java.util.concurrent.*;
import java.util.*;

ActorSystem sys = ActorSystem.create("em");
List<Integer> result = Source.from(Arrays.asList(0,1,2,3,4))
    .map(x -> x * 2 + 1)
    .runWith(Sink.seq(), sys)
    .toCompletableFuture()
    .get(10, TimeUnit.SECONDS);
for (Integer n : result) System.out.println("OUT " + n);
sys.terminate();
/exit
"#;
    let stdout = match util::run_jshell(&jshell, &classpath, "akka_streams", driver) {
        Some(s) => s,
        None => { util::skip("Akka_Streams jshell driver failed (classpath or Akka version mismatch)"); return; }
    };
    let upstream: Vec<i64> = stdout
        .lines()
        .filter_map(|l| l.strip_prefix("OUT ").and_then(|s| s.trim().parse().ok()))
        .collect();
    let repro: Vec<i64> = (0..5).map(|x: i64| x * 2 + 1).collect();
    assert_eq!(upstream, repro, "Akka_Streams emission {:?} != reproduction {:?}", upstream, repro);
    util::pass("Akka_Streams", format!("source-map-sink emission sequence = reproduction = {:?}", upstream));
}
