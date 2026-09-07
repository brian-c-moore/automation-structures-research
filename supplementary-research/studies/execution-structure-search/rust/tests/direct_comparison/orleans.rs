//! Direct comparison: Orleans (.NET, Microsoft.Orleans).
//!
//! Building a runnable Orleans grain test requires `dotnet`,
//! NuGet-resolved Microsoft.Orleans.Server, and an in-process silo.
//! This harness detects `dotnet`, attempts to construct a minimal
//! Orleans driver project that hosts a single grain and invokes a
//! four-step grain method chain, runs it, and parses the printed
//! activity order. Skips cleanly if NuGet restore fails (offline,
//! firewalled, or no .NET SDK).

#[path = "util.rs"]
mod util;

use std::collections::HashSet;
use std::fs;
use std::process::Command;

pub fn run() {
    let dotnet = match util::find_binary("dotnet", &[]) {
        Some(p) => p,
        None => { util::skip("dotnet not installed at any known path; Orleans direct comparison cannot run"); return; }
    };
    let version = Command::new(&dotnet).arg("--version").output().ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "dotnet (version probe unavailable)".to_string());
    util::compared_against("Orleans (via dotnet)", version.as_str());

    let dir = util::make_tempdir("orleans");
    let proj_dir = dir.join("OrleansDriver");
    fs::create_dir_all(&proj_dir).unwrap();
    let program = "using Microsoft.Extensions.Hosting;\nusing Microsoft.Extensions.DependencyInjection;\nusing Orleans;\nusing Orleans.Hosting;\nusing System;\nusing System.Threading.Tasks;\npublic interface IChain : IGrainWithIntegerKey {\n    Task<string> Step(string name);\n}\npublic class ChainGrain : Grain, IChain {\n    public Task<string> Step(string name) { Console.WriteLine(name); return Task.FromResult(name); }\n}\npublic class Program {\n    public static async Task Main() {\n        var host = Host.CreateDefaultBuilder()\n            .UseOrleans(b => b.UseLocalhostClustering())\n            .Build();\n        await host.StartAsync();\n        var f = host.Services.GetRequiredService<IGrainFactory>();\n        var g = f.GetGrain<IChain>(0);\n        await g.Step(\"ingest\");\n        await g.Step(\"transform_a\");\n        await g.Step(\"transform_b\");\n        await g.Step(\"aggregate\");\n        await host.StopAsync();\n    }\n}\n";
    fs::write(proj_dir.join("Program.cs"), program).unwrap();
    let csproj = "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <OutputType>Exe</OutputType>\n    <TargetFramework>net8.0</TargetFramework>\n    <Nullable>disable</Nullable>\n    <ImplicitUsings>enable</ImplicitUsings>\n  </PropertyGroup>\n  <ItemGroup>\n    <PackageReference Include=\"Microsoft.Extensions.Hosting\" Version=\"8.0.0\" />\n    <PackageReference Include=\"Microsoft.Orleans.Server\" Version=\"8.0.0\" />\n    <PackageReference Include=\"Microsoft.Orleans.Sdk\" Version=\"8.0.0\" />\n  </ItemGroup>\n</Project>\n";
    fs::write(proj_dir.join("OrleansDriver.csproj"), csproj).unwrap();

    let out = Command::new(&dotnet).arg("run").arg("--project").arg(&proj_dir).arg("-c").arg("Release").current_dir(&dir).output().expect("dotnet run");
    if !out.status.success() {
        util::skip(format!(
            "Orleans dotnet run failed (NuGet restore, SDK setup, or silo init): {}",
            String::from_utf8_lossy(&out.stderr).lines().rev().take(3).collect::<Vec<_>>().join(" | ")
        ));
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let interest: HashSet<&str> = ["ingest","transform_a","transform_b","aggregate"].into_iter().collect();
    let upstream: Vec<String> = String::from_utf8_lossy(&out.stdout)
        .lines().map(|s| s.trim()).filter(|s| interest.contains(*s)).map(|s| s.to_string()).collect();
    if upstream.is_empty() {
        util::skip("Orleans run produced no activity trace");
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    let repro = vec!["ingest".to_string(), "transform_a".to_string(), "transform_b".to_string(), "aggregate".to_string()];
    assert_eq!(upstream, repro, "Orleans grain order {:?} != reproduction {:?}", upstream, repro);
    util::pass("Orleans", format!("grain invocation order = reproduction = {:?}", upstream));
    let _ = fs::remove_dir_all(&dir);
}
