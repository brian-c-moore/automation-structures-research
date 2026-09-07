# Verification

Run formal checks in the pinned image. Pass subcommands after the image name so they use the container entrypoint and its recorded toolchain.

| Path | Purpose |
|---|---|
| `Dockerfile` | Pins base images, tool downloads, and the exact `automation-structures` crate archive by digest and checksum |
| `run_proofs.py` | Container entrypoint for discovery (`list`, `show`), execution (`run`), tool identity (`doctor`), and a runner self-test |
| `toolchain/` | Recorded TLA+ Tools JAR with its hash and upstream license notices |

The image extracts the immutable crates.io archive at `/opt/automation-structures`. The runner
checks its package version and `.cargo_vcs_info.json` commit against
`formal/implementation/AUTOMATION_STRUCTURES_CRATE.json` before discovering implementation proof,
mutation-control, or known-answer work items.

Build commands, selection tables, execution rules, and result interpretation are in [docs/reproducibility.md](../docs/reproducibility.md).
