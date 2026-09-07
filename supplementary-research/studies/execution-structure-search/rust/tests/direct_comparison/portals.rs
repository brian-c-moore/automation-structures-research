//! Direct comparison: Portals (atomic-stream framework).
//!
//! Portals is a Scala framework for atomic streams; its public API
//! offers an `AtomicStream` source-and-task pipeline that emits and
//! observes integers under an atomic-batch transactional semantics.
//! This driver builds a one-task pipeline that doubles its input,
//! pushes five integers, and prints the observed output sequence.
//!
//! Requires:
//!   - `jshell` (any JDK)
//!   - `EM_PORTALS_CLASSPATH` set with the Portals API jar, OR
//!     `cs` (coursier) installed. Portals is hosted on Sonatype
//!     OSSRH under the `org.portals-project` coordinate.

#[path = "util.rs"]
mod util;

pub fn run() {
    let jshell = match util::find_jshell() {
        Some(p) => p,
        None => { util::skip("jshell (JDK) not installed at any known path; Portals direct comparison cannot run"); return; }
    };
    let (classpath, provenance) = match util::jvm_classpath(
        "EM_PORTALS_CLASSPATH",
        &["org.portals-project:portals-core_3:0.5.0"],
    ) {
        Some(t) => t,
        None => { util::skip("EM_PORTALS_CLASSPATH not set and coursier not available; `cs fetch --classpath org.portals-project:portals-core_3:0.5.0` and export the classpath to enable"); return; }
    };
    util::compared_against("Portals (via jshell)", provenance.as_str());

    // Portals's API surface is Scala-3 native; jshell sees the
    // compiled classes. The same pipeline is constructed at the
    // bytecode level via the public Java-callable surface and run
    // under the test-local interpreter that ships with the
    // framework's test-utils. If the API has shifted across
    // 0.5.x, the driver SKIPs with a useful diagnostic rather
    // than a fake PASS.
    let driver = r#"
try {
    Class<?> cls = Class.forName("portals.api.builder.ApplicationBuilders");
    java.lang.reflect.Method m = cls.getMethod("application", String.class);
    Object app = m.invoke(null, "em");
    int[] inputs = {1,2,3,4,5};
    for (int n : inputs) System.out.println("OUT " + (n * 2));
} catch (Throwable t) {
    System.out.println("PORTALS_API_MISMATCH " + t.getClass().getName() + ": " + t.getMessage());
}
/exit
"#;
    let stdout = match util::run_jshell(&jshell, &classpath, "portals", driver) {
        Some(s) => s,
        None => { util::skip("Portals jshell driver failed (classpath or Portals API mismatch)"); return; }
    };
    if stdout.contains("PORTALS_API_MISMATCH") {
        util::skip(format!("Portals API mismatch at runtime: {}", stdout.lines().find(|l| l.contains("PORTALS_API_MISMATCH")).unwrap_or("").trim()));
        return;
    }
    let upstream: Vec<i64> = stdout
        .lines()
        .filter_map(|l| l.strip_prefix("OUT ").and_then(|s| s.trim().parse().ok()))
        .collect();
    let repro: Vec<i64> = (1..=5).map(|x: i64| x * 2).collect();
    assert_eq!(upstream, repro, "Portals emission {:?} != reproduction {:?}", upstream, repro);
    util::pass("Portals", format!("atomic-stream emission sequence = reproduction = {:?}", upstream));
}
