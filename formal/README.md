# Formal

This tree holds the formal artifact for Automation Structures: TLA+ models and proofs, TLC configurations, negative controls, correspondence records for the published Rust crate, and executable examples.

[docs/formal-methods.md](../docs/formal-methods.md) lists the formal work, what each part tries to establish, where its source is, and how a reviewer selects it. Formal tools run only through the container entrypoint at [verification/run_proofs.py](../verification/run_proofs.py); build and run instructions are in [docs/reproducibility.md](../docs/reproducibility.md).

| Directory | Contents |
|---|---|
| `structures/` | Catalog structure models, proofs, controls, reductions, refinements, separation witnesses |
| `execution/` | Execution carriers, refinements, separation witnesses |
| `composition/` | Composition core and structure-composition theorems |
| `construction/` | ALK construction: kernels, derivations, atomicity and governed-commit bridges |
| `assurance/` | Claim-relative ownership, TCB, delegation, transfer, guarantee, assurance, and placement models |
| `implementation/` | Immutable crates.io version, archive checksum, source commit, and source-locator identity for the canonical Rust implementation |
| `examples/` | Executable reconstructions and case studies ([README](examples/README.md)) |

The summary observation profiles are model-level representation studies, separate from the
published Rust correspondence records:

- [AuditSinkSummary](structures/AuditSink/refinement/AuditSinkSummary.tla) maps count, carry and
  latest operation plus a logical history to canonical AuditSink Record/stutter. Its proof checks
  summary binding, capacity and guard agreement under a natural lifetime bound and Nat-closed Hash.
- [ReductionSummary](structures/Reduction/refinement/ReductionSummary.tla) calls that same Record
  and maps count/carry to the ordered-prefix machine. No associativity is required.
- [SignalSummary](structures/Signal/refinement/SignalSummary.tla) adds listener positions and maps
  latest-change/catch-up behavior to Signal. It coalesces unobserved changes and refuses exhaustion;
  it does not model physical concurrency, generation-token reuse or operating-system wakes.

Use `run --contains Summary --area structures` through the documented pinned container entrypoint.
The profile has three parametric proof roots and 15 finite positive/control items. The six controls
target count, carry, latest, capacity, ordered input and premature delivery acknowledgement.
Logical history is not retained runtime evidence: these profiles provide no replay, recomputation
validation, cryptographic tamper detection, durable custody or compact Rust conformance claim.
The existing full-history model and implementation correspondence records retain their own scope.
