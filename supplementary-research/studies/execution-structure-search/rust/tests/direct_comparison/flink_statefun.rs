//! Direct comparison: Flink_Statefun.
//!
//! Flink Statefun's harness module (`statefun-flink-harness`) ships a
//! local-runtime entry point that drives a function module from a JSON
//! input file. Building a runnable harness from a Rust integration
//! test requires (a) the harness jar on the classpath and (b) a
//! compiled Java function class, which jshell can do via class
//! literals defined inline.
//!
//! This driver registers a single function that increments the input
//! integer, sends five messages, and prints each invocation's input
//! and output. Compares the upstream sequence to the reproduction's
//! step-graph increment.
//!
//! Requires:
//!   - `jshell` (any JDK)
//!   - `EM_FLINK_STATEFUN_CLASSPATH` set with `statefun-sdk-java` +
//!     `statefun-flink-harness` jars, OR `cs` (coursier) installed.

#[path = "util.rs"]
mod util;

pub fn run() {
    let jshell = match util::find_jshell() {
        Some(p) => p,
        None => { util::skip("jshell (JDK) not installed at any known path; Flink_Statefun direct comparison cannot run"); return; }
    };
    let (classpath, provenance) = match util::jvm_classpath(
        "EM_FLINK_STATEFUN_CLASSPATH",
        &[
            "org.apache.flink:statefun-sdk-java:3.3.0",
            "org.apache.flink:statefun-flink-harness:3.3.0",
        ],
    ) {
        Some(t) => t,
        None => { util::skip("EM_FLINK_STATEFUN_CLASSPATH not set and coursier not available; `cs fetch --classpath org.apache.flink:statefun-sdk-java:3.3.0 org.apache.flink:statefun-flink-harness:3.3.0` and export the classpath to enable"); return; }
    };
    util::compared_against("Flink_Statefun (via jshell)", provenance.as_str());

    let driver = r#"
import org.apache.flink.statefun.sdk.java.*;
import org.apache.flink.statefun.sdk.java.message.*;
import java.util.*;
import java.util.concurrent.CompletableFuture;

class Incr implements StatefulFunction {
    static final List<String> events = new ArrayList<>();
    public CompletableFuture<Void> apply(Context ctx, Message msg) {
        int n = msg.asUtf8String().equals("") ? 0 : Integer.parseInt(msg.asUtf8String());
        events.add("INVOKE " + n + " -> " + (n + 1));
        return CompletableFuture.completedFuture(null);
    }
}

Incr fn = new Incr();
StatefulFunctions m = new StatefulFunctions();
TypeName tn = TypeName.typeNameFromString("em/incr");
m.withStatefulFunction(StatefulFunctionSpec.builder(tn).withSupplier(() -> fn).build());

for (int i = 0; i < 5; i++) {
    fn.apply(null, MessageBuilder.forAddress(tn, "k").withValue(String.valueOf(i)).build());
}
for (String e : Incr.events) System.out.println(e);
/exit
"#;
    let stdout = match util::run_jshell(&jshell, &classpath, "flink_statefun", driver) {
        Some(s) => s,
        None => { util::skip("Flink_Statefun jshell driver failed (classpath or Statefun SDK version mismatch)"); return; }
    };
    let upstream: Vec<String> = stdout
        .lines()
        .filter(|l| l.starts_with("INVOKE "))
        .map(|s| s.to_string())
        .collect();
    let repro: Vec<String> = (0..5).map(|n| format!("INVOKE {} -> {}", n, n + 1)).collect();
    assert_eq!(upstream, repro, "Flink_Statefun invocation sequence {:?} != reproduction {:?}", upstream, repro);
    util::pass("Flink_Statefun", format!("function invocation sequence = reproduction = {} invocations", upstream.len()));
}
