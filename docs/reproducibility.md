# Reproducibility Guide

Current workspace development runs ordinary Cargo, Verus and selected formal-tool
commands directly against the existing source. Formal execution uses the pinned
Docker toolchain with the image entrypoint overridden by the selected tool. Reuse
the existing shared `rust/target` and Cargo cache, keep source read-only during
verification, and record the actual command, source identity, selected profile and
outcome. Audits run directly in AudiToad with reviewed baselines. No source
transport, disposable checkout or qualification harness is part of this workflow.

The research Rust workspace consumes `automation-structures =0.4.0` from crates.io.
Native examples use `formal/examples/rust/Cargo.toml` and the shared `../rust/target`.
The canonical descriptor pins the published archive's checksum and source commit;
the Dockerfile installs that archive at `/opt/automation-structures`.
Collection inputs can pin the actual source/model bytes in AudiToad before audit dispatch.
The [verification input roles](../verification/README.md) describe the archive
identity and proof source bindings.

## Rust workspace checks

From `formal/examples/rust`, fetch the locked dependencies once with network access,
then run the checks offline:

```text
cargo fetch --locked
cargo test --locked --offline --workspace
cargo clippy --locked --offline --workspace --all-targets -- -D warnings
```

## Build the verifier image

The image provides the pinned formal tools and published canonical archive. Run
selected formal tools directly by overriding its entrypoint.

From the repository root:

```text
docker build --pull=false --tag automation-structures-proofs verification
```

The Dockerfile pins its base images and downloaded tool artifacts by digest. The exact recorded TLA+ Tools JAR is included at `verification/toolchain/tla2tools.jar` because the upstream v1.8.0 pre-release asset is replaced by later builds. The build verifies its SHA-256 before using it. Its version, hash, source tag, and embedded license locations are recorded in `verification/toolchain/THIRD_PARTY_NOTICES.txt` and `verification/toolchain/SHA256SUMS`.

The JDK, Verus, and TLAPS packages are fetched automatically during an uncached build and verified against the checksums in the Dockerfile. A reviewer does not download or install those packages manually. Verifier 0.5.2 also installs Rustfmt and Clippy for the pinned Rust toolchain and fetches the published crate's locked dependencies. The build requires network access when these pinned inputs are not already cached. Formal runs use `--network none`.

## Host requirements and platform notes

Any host that can run `linux/amd64` containers works. The images are pinned to that platform, so on Apple Silicon and other ARM hosts they run under emulation and take correspondingly longer.

The checkout must be reachable by Docker's file sharing. On Docker Desktop, the repository path has to sit under a shared drive or directory, or the `--volume` mount fails with a path-not-shared error.

The Windows command examples use PowerShell, with `${PWD}` before the volume separator so the colon is not parsed as part of a variable name. Git Bash rewrites container paths in `--volume` arguments; prefix each `docker run` with `MSYS_NO_PATHCONV=1` and pass the host path in `C:/...` form. Cloning on Windows may also require `git clone -c core.longpaths=true` because some paths in this repository exceed 260 characters.

The repository's `.gitattributes` disables line-ending conversion so every clone is byte-exact on every platform. Do not renormalize or convert line endings: the whole-tree source fingerprint hashes raw file bytes, so any local rewrite reads as a source change.

The timeout bounds each tool process. A work item may start several processes, so it can take longer than that limit in total. Discovery prints the current work-item
count and selection fingerprint; use those instead of a historical count. Use focused selectors
for changed proof inputs and a complete primary run to establish a stable baseline. For later edits,
the [roadmap's verification rule](../ROADMAP.md#verification) explains when earlier results can cover
unchanged inputs. Use `--repeat 2` when the review specifically calls for a repeated-result comparison.

## Start with discovery

```text
docker run --rm --init --network none --read-only --cap-drop ALL --security-opt no-new-privileges --cpus 1 --memory 3g --memory-swap 3g --pids-limit 256 --volume "${PWD}:/source/automation-structure-research:ro" --tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777 automation-structures-proofs list
docker run --rm --init --network none --read-only --cap-drop ALL --security-opt no-new-privileges --cpus 1 --memory 3g --memory-swap 3g --pids-limit 256 --volume "${PWD}:/source/automation-structure-research:ro" --tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777 automation-structures-proofs show Budget
docker run --rm --init --network none --read-only --cap-drop ALL --security-opt no-new-privileges --cpus 1 --memory 3g --memory-swap 3g --pids-limit 256 --volume "${PWD}:/source/automation-structure-research:ro" --tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777 automation-structures-proofs run --subject Budget --dry-run --no-selection-table
```

`list` and `show` expose identifiers, areas, engines, artifact kinds, subjects, paths, and purposes. `run` refuses to execute without an explicit selector or `--all`.

Docker options before the image name bound CPU, memory, process count, network access, mounts, and temporary storage. `--init` installs the PID 1 reaper required for long TLAPS runs; the verifier refuses to start without it so exited proof-tool children cannot exhaust the process limit. Entrypoint options after the image name select formal work and control proof execution. The entrypoint does not inspect or manage version-control state.

## Select the smallest relevant run

| Reviewer intent | Entrypoint arguments |
|---|---|
| One named structure or theorem family | `run --subject Budget` |
| One exact discovered item | `run --id <identifier>` |
| One research area | `run --area execution` |
| One proof engine | `run --engine tlaps --area construction` |
| Negative controls and isolated baselines | `run --controls-only --area structures` |
| Complete ALK-SPEC audit boundary | `run --subject ALK-SPEC-1 --repeat 2 --json /out/alk-spec.json` |
| Supplementary study | `run --scope supplementary --area minimality` |
| Entire primary corpus | `run --all --workers 1` |
| Tool and source identity | `doctor` |
| Runner staging and outcome self-test | `self-test` |
| Selection count and fingerprints without execution | `run --scope all --all --dry-run --no-selection-table` |
| Conservative focused execution | `run --subject Budget --workers 1 --timeout 600 --fail-fast --no-selection-table` |

Available filters can be combined. Use `--no-selection-table` to suppress per-item rows while retaining the count and source and selection fingerprints. Use `list --help`, `show --help`, or `run --help` for the current argument surface.

Supplementary studies are included under `supplementary-research/` and use the same read-only source mount. The runner keeps them out of primary scope and exposes them only through `--scope supplementary`; no additional volume is required. Preserved Rust and Verus sources plus Python oracles are not registered with the entrypoint yet.

## Write machine-readable results

Create a host output directory outside the source repository and mount it separately:

```text
docker run --rm --init --network none --read-only --user 0:0 --cap-drop ALL --security-opt no-new-privileges --cpus 1 --memory 3g --memory-swap 3g --pids-limit 256 --volume "${PWD}:/source/automation-structure-research:ro" --volume "$PWD/../automation-structures-reviewer-output:/out" --volume automation-structures-proof-target:/target --env CARGO_TARGET_DIR=/target --tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777 automation-structures-proofs run --subject Budget --repeat 2 --json /out/budget.json
```

Reviewer output is not part of the source artifact. The runner refuses a JSON destination inside the mounted source tree. Do not copy result output into the repository.

## Execution rules

Implementation proofs and known-answer checks require an absolute `CARGO_TARGET_DIR`
bound to one persistent Docker volume, as in the result command above. Reuse that
volume across runs. Discovery and TLA-only selections need no Cargo target. Root
proofs use the selected source's existing Cargo gate and its manifest edition/dependencies;
each proof refresh removes only the subject package's compiled output so a warm
cache cannot masquerade as a new verification. Known-answer checks use the
published native runner and its declared fixture edition and lint policy. Cargo
lock metadata stays in temporary writable storage while the image's registry is
read-only. The explicit container user in the example can write the target volume;
the source and image remain read-only and networking remains disabled.

The runner copies selected TLA sources into temporary container storage before invoking static checks, SANY, TLC, or TLAPS. Verus mutations are also applied only to temporary copies. Each source mutant must leave exactly one Verus error while preserving the other positive verification results, repeat with the same result, and leave the complete mounted research-source fingerprint unchanged. Temporary work is always removed when the command exits.

The default timeout applies per tool process. `--workers` controls TLC's internal worker count; TLAPS uses one proof worker, and work items execute in a stable sequence. TLC controls and ALK vector suites use one worker so their signatures remain attributable. `--fail-fast` stops after the first unexpected result. `--repeat` accepts values from one through five. Docker CPU, memory, and process limits remain effective for every tool started by the entrypoint.

The runner rejects explicit `Isa` proof hints, proof leaves that cite more than one theorem from the pinned `SequenceTheorems` module, unmatched `_NEG` modules, and orphaned isolated configurations during discovery. The pinned Isabelle installation remains available to TLAPS internally, but proof sources may not select that backend directly. A sequence-library premise and its consumer must be separated by a named, typed intermediate fact rather than left for one backend call to discover. Every TLC result must report at least one distinct state. ALK-SPEC adds exact positive state counts, exact vector trace-prefix counts, exact control invariant names and exit code, an exact 56-obligation TLAPS count, three SANY parses, a reference-vector and generated-module contract, and an 11-mutation checker self-test. Use a dry run to confirm current counts and fingerprints before execution.

## Interpret results

| Result | Meaning |
|---|---|
| TLC pass | The selected invariant or property held in the configured finite state space |
| Expected TLC violation | The named negative control reached its intended violating trace |
| ALK vector pass | Every compatible vector in the selected profile reached the registered terminal outcome and exact trace-prefix state count |
| TLAPS pass | The written obligations were proved under the module's definitions and assumptions |
| SANY or static pass | The selected syntax, file inventory, roots, paths, and binding contract matched the registered boundary |
| Verus pass | The selected Rust contracts were verified for the compiled proof surface |
| Expected Verus rejection | The positive source verified, the named mutant produced one isolated error twice, the other positive verification results remained verified, and mounted-source custody remained stable |
| Rust known-answer pass | The compiled implementation returned the recorded output for the selected inputs |

No result establishes completeness, universality, production deployment conformance, or behavior outside its premises. A control establishes sensitivity only to its named defect. A finite model result is not an unbounded theorem. A theorem over a model is not an implementation proof. A known-answer check is not exhaustive input coverage.

Machine-readable output records the selected work-item digest, runner hash, pre-run and post-run source fingerprints, repeat stability, and individual signatures. Record the exact Docker image ID separately with `docker image inspect --format "{{.Id}}" automation-structures-proofs`, and run that immutable ID when collecting the final receipt. Keep the image ID and invocation alongside the result JSON; the JSON does not contain the image ID. A dry run prints the source and selection fingerprints without starting a formal tool. A source change during execution fails the run. Each run reports the exact current selection and outcome to a caller-selected external path; no source-tree status file is rewritten by the runner.
