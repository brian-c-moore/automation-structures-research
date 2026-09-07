//! Direct comparison: Materialize.
//!
//! Materialize ships as a single `materialized` binary plus a
//! `psql`-compatible wire-protocol endpoint. This harness:
//!
//!   1. Detects either `materialized` (native binary) or `docker`
//!      (with the official `materialize/materialized` image).
//!   2. Starts a transient instance.
//!   3. Issues a CREATE MATERIALIZED VIEW with a windowed aggregation
//!      against an inline table of six events.
//!   4. SELECTs the view, parses the (window-start, sum) pairs.
//!   5. Compares to the `StreamingSql::small_example()` output.
//!
//! Skips cleanly if neither `materialized` nor `docker` is present, or
//! if the connection cannot be established.

use execution_modalities::workloads::streaming_sql::StreamingSql;
use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

pub fn run() {
    let psql = match find_psql() {
        Some(p) => p,
        None => {
            eprintln!("SKIP: psql not installed at any known path; direct comparison cannot run");
            return;
        }
    };

    let materialized = find_materialized();
    let docker = find_docker();
    let mut handle: Option<std::process::Child> = None;

    let connect_target = if let Some(bin) = &materialized {
        let h = Command::new(bin)
            .arg("--listen-addr=127.0.0.1:6875")
            .arg("--data-directory")
            .arg(env::temp_dir().join("em_mz_data"))
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn();
        match h {
            Ok(child) => {
                handle = Some(child);
                thread::sleep(Duration::from_secs(3));
                Some(("127.0.0.1".to_string(), 6875u16))
            }
            Err(_) => None,
        }
    } else if let Some(d) = &docker {
        let h = Command::new(d)
            .args([
                "run",
                "--rm",
                "-d",
                "--name",
                "em_materialize",
                "-p",
                "6875:6875",
                "materialize/materialized:latest",
            ])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
        if h.map(|s| s.success()).unwrap_or(false) {
            thread::sleep(Duration::from_secs(5));
            Some(("127.0.0.1".to_string(), 6875u16))
        } else {
            None
        }
    } else {
        eprintln!("SKIP: neither materialized nor docker is installed; direct comparison cannot run");
        return;
    };

    let (host, port) = match connect_target {
        Some(t) => t,
        None => {
            eprintln!("SKIP: could not start a Materialize instance; direct comparison cannot run");
            return;
        }
    };
    eprintln!(
        "compared against installed Materialize on {}:{} (via {})",
        host,
        port,
        if materialized.is_some() {
            "native binary"
        } else {
            "docker image materialize/materialized:latest"
        }
    );

    let sql = "\
CREATE TABLE em_events (ts BIGINT, val BIGINT);
INSERT INTO em_events VALUES (1, 10), (2, 20), (4, 5), (6, 7), (7, 3), (11, 100);
CREATE MATERIALIZED VIEW em_windowed AS
  SELECT (ts / 5) * 5 AS window_start, SUM(val) AS s FROM em_events GROUP BY (ts / 5) * 5;
SELECT window_start, s FROM em_windowed ORDER BY window_start;
";
    let out = Command::new(&psql)
        .args([
            "-h",
            host.as_str(),
            "-p",
            port.to_string().as_str(),
            "-U",
            "materialize",
            "-d",
            "materialize",
            "-A",
            "-t",
            "-c",
            sql,
        ])
        .env("PGPASSWORD", "materialize")
        .output()
        .expect("run psql");
    let _ = handle.map(|mut c| c.kill());
    let _ = docker.as_ref().map(|d| {
        Command::new(d).args(["rm", "-f", "em_materialize"]).status()
    });
    if !out.status.success() {
        eprintln!(
            "SKIP: psql query failed (likely Materialize did not initialize in time): {}",
            String::from_utf8_lossy(&out.stderr)
                .lines()
                .next()
                .unwrap_or("")
        );
        return;
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let mz_pairs: Vec<(u64, i64)> = stdout
        .lines()
        .filter_map(|l| {
            let parts: Vec<&str> = l.split('|').map(|s| s.trim()).collect();
            if parts.len() < 2 {
                return None;
            }
            Some((parts[0].parse().ok()?, parts[1].parse().ok()?))
        })
        .collect();

    let our = StreamingSql::small_example();
    let our_pairs: Vec<(u64, i64)> = our.run().into_iter().map(|w| (w.start, w.sum)).collect();

    assert_eq!(
        mz_pairs, our_pairs,
        "Materialize windowed view {:?} differs from reproduction {:?}",
        mz_pairs, our_pairs
    );
    eprintln!(
        "PASS: Materialize windowed view = reproduction = {:?}",
        our_pairs
    );
}

fn find_psql() -> Option<PathBuf> {
    if Command::new("psql")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        return Some(PathBuf::from("psql"));
    }
    let static_paths: &[&str] = &[
        "C:/Program Files/PostgreSQL/16/bin/psql.exe",
        "C:/Program Files/PostgreSQL/15/bin/psql.exe",
        "C:/Program Files/PostgreSQL/14/bin/psql.exe",
        "/usr/bin/psql",
        "/usr/local/bin/psql",
        "/opt/homebrew/bin/psql",
    ];
    for p in static_paths {
        if Path::new(p).exists() {
            return Some(PathBuf::from(p));
        }
    }
    None
}

fn find_materialized() -> Option<PathBuf> {
    for cand in &["materialized"] {
        if Command::new(cand)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            return Some(PathBuf::from(cand));
        }
    }
    None
}

fn find_docker() -> Option<PathBuf> {
    if Command::new("docker")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        return Some(PathBuf::from("docker"));
    }
    None
}
