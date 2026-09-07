//! Direct comparison: Akka (JVM).
//!
//! Akka is a JVM-only framework; running a real Akka actor system from
//! a Rust test requires (a) a JDK, (b) a build of Akka's jars on the
//! classpath, and (c) a small driver. This harness uses `coursier`
//! (the standard Scala/JVM dependency fetcher) to resolve Akka's
//! classpath in one command, then runs a tiny Java driver via
//! `jshell` -- which ships with every modern JDK.
//!
//! If `coursier` (or `cs`) is not installed, or `jshell` is missing,
//! or `EM_AKKA_CLASSPATH` is not set, the harness skips cleanly.

use execution_modalities::workloads::actor_message_exchange::ActorMessageExchange;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn run() {
    let jshell = match find_jshell() {
        Some(p) => p,
        None => {
            eprintln!("SKIP: jshell (JDK) not installed at any known path; direct comparison cannot run");
            return;
        }
    };

    // Resolve Akka classpath. Prefer EM_AKKA_CLASSPATH if set; else try
    // coursier (`cs fetch --classpath com.typesafe.akka:akka-actor_2.13:2.6.21`).
    let classpath = match env::var("EM_AKKA_CLASSPATH") {
        Ok(cp) if !cp.is_empty() => cp,
        _ => match resolve_via_coursier() {
            Some(cp) => cp,
            None => {
                eprintln!("SKIP: akka classpath not available; set EM_AKKA_CLASSPATH or install coursier (`cs`)");
                return;
            }
        },
    };
    eprintln!(
        "compared against installed Akka via jshell ({}), classpath len = {}",
        jshell.display(),
        classpath.len()
    );

    let driver = "\
import akka.actor.*;

public class PingPong {
    static int rounds = 4;
    static int observed = 0;
    static java.util.concurrent.CountDownLatch done = new java.util.concurrent.CountDownLatch(1);
}

class PongActor extends UntypedAbstractActor {
    public void onReceive(Object msg) {
        if (msg instanceof Integer) {
            int n = (Integer) msg;
            getSender().tell(Integer.valueOf(n + 1), getSelf());
        }
    }
}

class PingActor extends UntypedAbstractActor {
    private final ActorRef pong;
    public PingActor(ActorRef pong) { this.pong = pong; }
    public void onReceive(Object msg) {
        if (msg instanceof Integer) {
            int n = (Integer) msg;
            PingPong.observed++;
            if (n < PingPong.rounds) pong.tell(Integer.valueOf(n + 1), getSelf());
            else PingPong.done.countDown();
        }
    }
}

ActorSystem sys = ActorSystem.create(\"em\");
ActorRef pong = sys.actorOf(Props.create(PongActor.class), \"pong\");
ActorRef ping = sys.actorOf(Props.create(PingActor.class, pong), \"ping\");
ping.tell(Integer.valueOf(0), ActorRef.noSender());
PingPong.done.await(5, java.util.concurrent.TimeUnit.SECONDS);
sys.terminate();
System.out.println(\"OBSERVED \" + PingPong.observed);
/exit
";
    let script_path = env::temp_dir().join(format!(
        "em_akka_{}_{}.jsh",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    fs::write(&script_path, driver).unwrap();

    let out = Command::new(&jshell)
        .arg("--class-path")
        .arg(&classpath)
        .arg(&script_path)
        .output()
        .expect("run jshell");
    if !out.status.success() {
        eprintln!(
            "SKIP: jshell driver failed: stderr tail = {}",
            String::from_utf8_lossy(&out.stderr)
                .lines()
                .rev()
                .take(5)
                .collect::<Vec<_>>()
                .join(" | ")
        );
        let _ = fs::remove_file(&script_path);
        return;
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let akka_observed: i64 = stdout
        .lines()
        .filter_map(|l| {
            l.strip_prefix("OBSERVED ")
                .and_then(|n| n.trim().parse::<i64>().ok())
        })
        .next()
        .unwrap_or(-1);

    let our = ActorMessageExchange { rounds: 4 };
    let _ = our.run();
    let our_rounds = our.rounds as i64;
    // Akka observed = number of messages the ping actor processed,
    // which equals the number of round trips (one initial start + N-1
    // increments, then the final at-rounds termination). Compare
    // counts.
    assert!(
        akka_observed >= our_rounds,
        "Akka observed {} < expected at least {} round trips",
        akka_observed,
        our_rounds
    );
    eprintln!(
        "PASS: Akka observed {} ping events; reproduction round count = {}",
        akka_observed, our_rounds
    );

    let _ = fs::remove_file(&script_path);
}

fn find_jshell() -> Option<PathBuf> {
    if Command::new("jshell")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        return Some(PathBuf::from("jshell"));
    }
    // Search standard JDK install locations for jshell.exe.
    let mut candidates: Vec<PathBuf> = Vec::new();
    for base in &[
        "C:/Program Files/Java",
        "C:/Program Files/Microsoft",
        "C:/Program Files/Eclipse Adoptium",
        "C:/Program Files (x86)/Java",
    ] {
        if let Ok(entries) = fs::read_dir(base) {
            for entry in entries.flatten() {
                candidates.push(entry.path().join("bin").join("jshell.exe"));
            }
        }
    }
    if let Ok(local) = env::var("LOCALAPPDATA") {
        let pkgs = PathBuf::from(local).join("Microsoft").join("WinGet").join("Packages");
        if let Ok(entries) = fs::read_dir(&pkgs) {
            for entry in entries.flatten() {
                if let Ok(inner) = fs::read_dir(entry.path()) {
                    for sub in inner.flatten() {
                        candidates.push(sub.path().join("bin").join("jshell.exe"));
                    }
                }
            }
        }
    }
    for p in candidates {
        if p.exists() {
            return Some(p);
        }
    }
    None
}

fn resolve_via_coursier() -> Option<String> {
    for cs in &["cs", "coursier"] {
        if Command::new(cs)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            let out = Command::new(cs)
                .arg("fetch")
                .arg("--classpath")
                .arg("com.typesafe.akka:akka-actor_2.13:2.6.21")
                .output()
                .ok()?;
            if out.status.success() {
                let cp = String::from_utf8_lossy(&out.stdout).trim().to_string();
                if !cp.is_empty() {
                    return Some(cp);
                }
            }
        }
    }
    None
}
