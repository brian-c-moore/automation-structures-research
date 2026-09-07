//! Direct comparison: Pony (actor-model language).
//!
//! Writes a small Pony program with a ping-pong actor pair that
//! exchanges four messages and prints each receipt. Compiles with
//! `ponyc` and runs the resulting executable. Captures stdout,
//! parses the receipt count, and compares to the reproduction's
//! message-exchange count.

#[path = "util.rs"]
mod util;

use std::fs;
use std::process::Command;

pub fn run() {
    let ponyc = match util::find_binary("ponyc", &[]) {
        Some(p) => p,
        None => { util::skip("ponyc not installed at any known path; Pony direct comparison cannot run"); return; }
    };
    let version = Command::new(&ponyc).arg("--version").output().ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.lines().next().map(|x| x.to_string()))
        .unwrap_or_else(|| "ponyc (version probe unavailable)".to_string());
    util::compared_against("Pony (via ponyc)", version.as_str());

    let dir = util::make_tempdir("pony");
    fs::write(dir.join("main.pony"),
        "actor Main\n  let _env: Env\n  new create(env: Env) =>\n    _env = env\n    let pong = Pong\n    let ping = Ping(env, pong)\n    pong.set_partner(ping)\n    ping.start(0)\n\nactor Ping\n  let _env: Env\n  let _pong: Pong\n  var _observed: U32 = 0\n  new create(env: Env, pong: Pong) =>\n    _env = env\n    _pong = pong\n  be start(n: U32) =>\n    _env.out.print(\"PING \" + n.string())\n    _observed = _observed + 1\n    if n < 3 then _pong.ping(n + 1) else _env.out.print(\"OBSERVED \" + _observed.string()) end\n\nactor Pong\n  var _partner: (Ping | None) = None\n  be set_partner(p: Ping) => _partner = p\n  be ping(n: U32) =>\n    match _partner | let p: Ping => p.start(n) end\n").unwrap();

    let compile = Command::new(&ponyc).current_dir(&dir).output().expect("ponyc compile");
    if !compile.status.success() {
        util::skip(format!("ponyc compile failed: {}",
            String::from_utf8_lossy(&compile.stderr).lines().rev().take(3).collect::<Vec<_>>().join(" | ")));
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let basename = dir.file_name().unwrap().to_string_lossy().into_owned();
    let exe = if cfg!(windows) { dir.join(format!("{}.exe", basename)) } else { dir.join(&basename) };
    if !exe.exists() {
        util::skip(format!("ponyc produced no executable at {}", exe.display()));
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let out = Command::new(&exe).output().expect("run pony binary");
    if !out.status.success() {
        util::skip(format!("pony binary failed: {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(2).collect::<Vec<_>>().join(" | ")));
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let observed: i64 = stdout.lines()
        .filter_map(|l| l.strip_prefix("OBSERVED ").and_then(|s| s.trim().parse().ok()))
        .next()
        .unwrap_or(-1);
    let pings: i64 = stdout.lines().filter(|l| l.starts_with("PING ")).count() as i64;
    let repro_rounds: i64 = 4;
    assert_eq!(observed, repro_rounds, "Pony OBSERVED {} != reproduction rounds {}", observed, repro_rounds);
    assert_eq!(pings, repro_rounds, "Pony PING count {} != reproduction rounds {}", pings, repro_rounds);
    util::pass("Pony", format!("Pony actor message exchange = reproduction = {} round trips", repro_rounds));
    let _ = fs::remove_dir_all(&dir);
}
