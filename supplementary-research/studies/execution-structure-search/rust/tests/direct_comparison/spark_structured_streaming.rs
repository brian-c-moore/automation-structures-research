//! Direct comparison: Spark Structured Streaming via PySpark.
//!
//! Spins up a local SparkSession, creates a streaming DataFrame
//! from `format("rate")`, applies a structured transform
//! (`value * 2`), writes to an in-memory sink, sleeps long enough for
//! at least one micro-batch to commit, queries the sink table, and
//! asserts the doubled values appear as a non-empty subset of the
//! expected arithmetic progression.
//!
//! Requires `pyspark` (which transitively requires a JDK and, on
//! Windows, Hadoop `winutils`). Skips cleanly if any layer is
//! missing.

#[path = "util.rs"]
mod util;

use std::fs;
use std::process::Command;

pub fn run() {
    let python = match util::find_python() {
        Some(p) => p,
        None => { util::skip("python not installed; Spark_Structured_Streaming direct comparison cannot run"); return; }
    };
    let version = match util::python_has_package(&python, "pyspark") {
        Some(v) => v,
        None => { util::skip(format!("pyspark not installed under {}; `pip install pyspark` to enable", python.display())); return; }
    };
    util::compared_against("Spark_Structured_Streaming (via pyspark)", version.as_str());

    let dir = util::make_tempdir("spark_ss");
    let script = dir.join("ss.py");
    fs::write(&script,
        "import time, sys\nfrom pyspark.sql import SparkSession\nfrom pyspark.sql.functions import col\ntry:\n    spark = SparkSession.builder.master('local[2]').appName('em').config('spark.ui.enabled','false').getOrCreate()\nexcept Exception as e:\n    print('SPARK_INIT_FAIL', e, file=sys.stderr); sys.exit(2)\ndf = spark.readStream.format('rate').option('rowsPerSecond','5').option('numPartitions','1').load()\ndoubled = df.select((col('value')*2).alias('d'))\nq = doubled.writeStream.format('memory').queryName('em').outputMode('append').start()\ntime.sleep(3)\nrows = spark.sql('select d from em order by d').collect()\nfor r in rows: print(r.d)\nq.stop()\nspark.stop()\n").unwrap();

    let out = Command::new(&python).arg(&script).output().expect("pyspark run");
    if !out.status.success() {
        let combined = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        util::skip(format!("pyspark Structured Streaming failed (often: JAVA_HOME unset, winutils missing, port conflict): {}",
            combined.lines().rev().take(3).collect::<Vec<_>>().join(" | ")));
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let upstream: Vec<i64> = String::from_utf8_lossy(&out.stdout)
        .lines().filter_map(|l| l.trim().parse().ok()).collect();
    assert!(!upstream.is_empty(), "Spark micro-batch sink emitted no rows");
    for v in &upstream {
        assert!(*v >= 0 && *v % 2 == 0, "Spark micro-batch row {} is not an even non-negative integer", v);
    }
    let repro: Vec<i64> = (0i64..(upstream.len() as i64)).map(|x| x * 2).collect();
    assert_eq!(upstream, repro, "Spark micro-batch output {:?} != reproduction {:?}", upstream, repro);
    util::pass("Spark_Structured_Streaming", format!("micro-batch output ({} rows) = reproduction = {:?}", upstream.len(), upstream));
    let _ = fs::remove_dir_all(&dir);
}
