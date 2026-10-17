# Verification

Run current local formal checks directly with the pinned image's recorded tools,
overriding its entrypoint for the selected Cargo, Verus, TLC or TLAPS command.
Use the existing source, shared target and Cargo cache in place. The Python
entrypoint and published-image recipes below retain their historical roles;
they are not the current workspace's development or audit workflow.

| Path | Purpose |
|---|---|
| `Dockerfile` | Pins base images, tool downloads, and the exact `automation-structures` crate archive by digest and checksum |
| `run_proofs.py` | Container entrypoint for discovery (`list`, `show`), execution (`run`), tool identity (`doctor`), and a runner self-test |
| `toolchain/` | Recorded TLA+ Tools JAR with its hash and upstream license notices |

`formal/implementation/AUTOMATION_STRUCTURES_CRATE.json` pins the published
`automation-structures` 0.4.0 archive, checksum and source commit. The native research
workspace consumes exact version 0.4.0 from crates.io. The image installs the archive
at `/opt/automation-structures`, matching the descriptor and `.cargo_vcs_info.json`.
Record source hashes, selected profiles, commands and actual outcomes. AudiToad reads
pinned actual files and retained results through its reviewed collection inputs.

Derivation records and generated proof metadata retain their original archive or
local 0.3.2 locators. Run Cargo, Verus, TLC and TLAPS directly with the pinned tools.

The version-bound 0.3.2 implementation profile accounts for 37 source modules and 141 attributed mutations,
plus the existing detector self-test. The additional module is the MinimumSelection
composition of OrderingPass, Hard selection, Cursor and Buffer. Its new control omits the
actual Buffer publication of a tied item and requires the exact selected-prefix invariant
rejection. That declared control has no acceptance until its positive, mutant and restoration
execute as specified. Both local and actually published 0.3.2 select this same profile,
including its 15 adapted action selectors or mutation bodies. Retained 0.2.3, 0.2.4, 0.3.0 and 0.3.1 inputs
retain 36 modules and 140 mutations. An unknown version requires an explicit reviewed profile. Neither
count establishes complete semantics or transfers a Hard winner theorem into all-ties coverage.

The current implementation profile declares its action selectors separately from the
historical registry. Storage adapters and delegated observations retain their actual owner boundaries:
Sequential, StepGraph and StreamGraph terminal controls mutate the public terminal actions;
the ForkJoin stale-snapshot control targets the materialized Vec snapshot's physical copy
binding, with no claim about the borrowed snapshot profile. Missing diagnostic partitions
remain unqualified until they are explicitly reviewed and run against the selected source.
The graph pair-removal control preserves the current Registry return's `Some((key, ()))`
shape while omitting the same deletion; historical versions retain their original pair return.

Build commands, selection tables, execution rules, and result interpretation are in [docs/reproducibility.md](../docs/reproducibility.md).
