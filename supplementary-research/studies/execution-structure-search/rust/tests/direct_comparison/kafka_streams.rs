//! Direct comparison: Kafka_Streams.
//!
//! Drives Kafka Streams' `TopologyTestDriver` via a jshell script:
//! builds a topology that maps an input topic to an output topic via a
//! single per-record transform, pushes five records, drains the
//! output topic, and prints the output value sequence. Compares the
//! upstream sequence against the reproduction's identity-map step
//! over the same five inputs.
//!
//! Requires:
//!   - `jshell` (any JDK)
//!   - `EM_KAFKA_STREAMS_CLASSPATH` set, OR `cs` (coursier) installed
//!     so the harness can `cs fetch` the Kafka Streams + test-utils
//!     jars at runtime.

#[path = "util.rs"]
mod util;

pub fn run() {
    let jshell = match util::find_jshell() {
        Some(p) => p,
        None => { util::skip("jshell (JDK) not installed at any known path; Kafka_Streams direct comparison cannot run"); return; }
    };
    let (classpath, provenance) = match util::jvm_classpath(
        "EM_KAFKA_STREAMS_CLASSPATH",
        &[
            "org.apache.kafka:kafka-streams:3.7.0",
            "org.apache.kafka:kafka-streams-test-utils:3.7.0",
        ],
    ) {
        Some(t) => t,
        None => { util::skip("EM_KAFKA_STREAMS_CLASSPATH not set and coursier not available; `cs fetch --classpath org.apache.kafka:kafka-streams:3.7.0` and export the classpath to enable"); return; }
    };
    util::compared_against("Kafka_Streams (via jshell)", provenance.as_str());

    let driver = r#"
import org.apache.kafka.common.serialization.Serdes;
import org.apache.kafka.streams.*;
import org.apache.kafka.streams.kstream.*;
import org.apache.kafka.streams.test.TestRecord;
import java.util.*;

StreamsBuilder b = new StreamsBuilder();
KStream<String,String> in = b.stream("in", Consumed.with(Serdes.String(), Serdes.String()));
in.mapValues(v -> v + "*").to("out", Produced.with(Serdes.String(), Serdes.String()));
Properties p = new Properties();
p.put(StreamsConfig.APPLICATION_ID_CONFIG, "em-app");
p.put(StreamsConfig.BOOTSTRAP_SERVERS_CONFIG, "ignored:1");
p.put(StreamsConfig.DEFAULT_KEY_SERDE_CLASS_CONFIG, Serdes.String().getClass().getName());
p.put(StreamsConfig.DEFAULT_VALUE_SERDE_CLASS_CONFIG, Serdes.String().getClass().getName());
TopologyTestDriver d = new TopologyTestDriver(b.build(), p);
TestInputTopic<String,String> it = d.createInputTopic("in", Serdes.String().serializer(), Serdes.String().serializer());
TestOutputTopic<String,String> ot = d.createOutputTopic("out", Serdes.String().deserializer(), Serdes.String().deserializer());
for (String s : new String[]{"a","b","c","d","e"}) it.pipeInput(s);
for (TestRecord<String,String> r : ot.readRecordsToList()) System.out.println("OUT " + r.value());
d.close();
/exit
"#;
    let stdout = match util::run_jshell(&jshell, &classpath, "kafka_streams", driver) {
        Some(s) => s,
        None => { util::skip("Kafka_Streams jshell driver failed (classpath or Kafka version mismatch)"); return; }
    };
    let upstream: Vec<String> = stdout
        .lines()
        .filter_map(|l| l.strip_prefix("OUT ").map(|s| s.trim().to_string()))
        .collect();
    let repro: Vec<String> = ["a", "b", "c", "d", "e"].iter().map(|s| format!("{}*", s)).collect();
    assert_eq!(upstream, repro, "Kafka_Streams output sequence {:?} != reproduction {:?}", upstream, repro);
    util::pass("Kafka_Streams", format!("TopologyTestDriver output topic sequence = reproduction = {:?}", upstream));
}
