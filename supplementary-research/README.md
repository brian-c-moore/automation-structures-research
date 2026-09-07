# Supplementary Research

This public corpus preserves valid negative science, failed experiments that expose a useful boundary, and research artifacts that do not directly support the retained Automation Structures claims. It is included so readers can inspect what was tried, what failed, which boundaries survived, and what remains untested. Failed work is retained when the failure teaches something about the method, model, or claim.

Nothing in this directory establishes completeness, universality, final catalog membership, or acceptance of a retained claim. A passing finite model applies only to its stated configuration. An invalidated experiment documents what was tried and why it did not support its original conclusion.

## Layout

All scientific artifacts are grouped under `studies/`. This README is the only Markdown document in the corpus. The tree is exploratory rather than primary evidence: a study may preserve incomplete comparisons or implementations when its executable subset and evidence ceiling are stated explicitly. Empty groups, silent skips, broken referents, and unbounded conclusions receive no evidence credit.

| Study | Files | Question | Retained material | Current standing |
|---|---:|---|---|---|
| `studies/domain-corpora/` | 307 | Can the vocabulary reconstruct algorithmic, cryptographic, and out-of-family systems without hiding residual behavior? | Rust crates, Python oracles, TLA+ models, TLC configurations, Verus sources, manifests, vectors, and lockfiles | Preserved reconstruction and negative-use science; not current primary evidence |
| `studies/execution-structure-search/` | 410 | Did the examined systems require another base execution structure? | 134 framework configurations, TLA+ candidates and comparisons, Rust sources, Verus sources, and crate metadata | The reported search found no admitted fifth structure among the systems examined; several old test mechanisms were invalidated and remain only as failed-method science |
| `studies/irreducibility/` | 62 | Which tested check-act separations make a named violation reachable? | 31 paired TLA+ models and configurations | Evidence for the tested seams; no general necessity claim |
| `studies/minimality/` | 7 | Which tested reductions succeed, fail, or expose an inadequate target model? | One backtracking model-degeneracy proof, two positive models, and one negative control | Catalog-relative evidence only; no global minimality order |

The file counts describe the current tree. They are inventory facts, not evidence counts.

## Reported results and limits

### Catalog census

The retained working record reports seven connective forms: Projection, Cursor, Accumulator, Marker, Counter, Buffer, and OrderingPass. Window and Threshold were rejected as independent forms. Guard was classified as an obligation-boundary mechanism rather than another connective form. The out-of-family trial did not surface another structure in the three examined domains. These results cover the systems examined and can be revised by new residuals.

### Domain corpora

The algorithm and cryptography corpora record reconstruction attempts, execution-structure admission checks, implementation comparisons, and selected refinement models. The out-of-family crate contains term rewriting, computer algebra, and proof-search cases used to challenge the catalog. A result that one examined construction does not require a structure does not generalize to the whole domain.

The cryptography Rust corpus registers exactly seven executable algorithms: SHA-256, SHA-3-256, BLAKE3, ChaCha20, HMAC-SHA-256, HKDF-SHA-256, and PBKDF2-HMAC-SHA-256. Its corpus gate rejects empty groups, requires every registered algorithm to run, and treats a missing Python oracle as failure. The BLAKE3 Python binding is pinned in `rust/python/requirements.txt`; install that file into the interpreter named by `PYTHON` before running the crate tests. The algorithm-corpus Verus source contains 88 `external_body` boundaries and 83 uninterpreted specification functions; the cryptography Verus source contains 127 and 45, respectively. Both trees therefore receive no algorithm-conformance credit. Those boundaries preserve exploratory definitions and contracts, not machine-checked equivalence to the Rust algorithms.

`MemoizationComposition.tla` instantiates the canonical `ResourceRegistry`. Its traversal and reduction steps remain inline because the fixed canonical domains cannot be re-armed for each memo cell. The result covers that registry instance plus the written inline model; it is not a three-component canonical composition theorem.

### Execution-structure search

The search classified 134 named systems and patterns into 21 observed tuples over modality, invocation, topology, dependencies, lifecycle, and workload. No examined candidate met every recorded admission gate for another base carrier. Several historical test mechanisms were rejected because they compared a value with itself, selected constants that satisfied the property by construction, ignored the selected modality, or fixed the candidate class before exploration. Their source remains as a record of those failure modes and receives no credit for the rejected conclusion.

The 58 direct-comparison Rust sources are one such invalidated mechanism. Their former test aggregator reported success after environment-dependent skips, so it was removed. The 70 scenario-specific trace-comparison sources are another: representative cases compare two hand-written encodings of the same expected sequence, and at least one claimed StreamGraph reproduction never invokes the driver. Their aggregator was removed and the sources remain non-executable under `trace_equivalence/`. The three tier-wide Rust aggregators and the `modalities` CLI were also removed: they labeled all configurations as framework reproductions even though the test driver supports only four local workload names, collapses many domain policy values, and leaves most recorded configurations unsupported or incompatible. The configurations remain classification records. None of these invalidated sources receives pass credit from its absence in a run.

Four execution-search Verus modality files are also invalidated failed-method records. Five former functions asserted uninterpreted predicates through `external_body` and returned `true`; two KAT binaries then counted those returns as passes. The functions and both non-runnable KAT files have been removed. One sequential-to-step-graph contract over its configured states remains as source, but this directory has no verifier wrapper and supplies no executable evidence or general execution-structure refinement result.

### Irreducibility and minimality

The irreducibility study asks whether a modeled invariant fails after a fused check and act is separated or a defining guard is removed. The minimality study asks whether a target can be reconstructed from the remaining catalog, admitted connective forms, and declared relies. Both results depend on the written target, mapping, observation relation, and model boundary.

## File-retention rules

The corpus keeps unique source, configurations, witnesses, structured data, test vectors, and independently runnable crate boundaries. Identical small TLC configuration files remain where each one names a separate model invocation. Shared Rust source remains duplicated where separate study crates need an isolated copy. Those choices favor attributable study execution over a cross-study build dependency.

The corpus does not keep caches, build directories, prover binaries, downloaded archives, logs, model-checker state, generated source-tree reports, host launchers, or per-study wrapper scripts. Reviewer behavior belongs in the single container entrypoint at `../verification/run_proofs.py`.

## Reviewer navigation

Mount the Automation Structures repository once, then use the container entrypoint:

```text
run_proofs.py list --scope supplementary
run_proofs.py list --scope supplementary --area domain-corpora
run_proofs.py run --scope supplementary --area minimality --dry-run
run_proofs.py run --scope supplementary --area irreducibility
run_proofs.py run --scope supplementary --area execution-structure-search --contains candidate
```

The current supplementary selectors cover the TLA+ and TLAPS files only. Rust and Verus files are study sources rather than runner work items. Their results depend on the exact crate tests and Python oracle contracts named by each study; invalidated probes are non-executable source and receive no pass credit. The container commands and result interpretation rules are in `../docs/reproducibility.md`. Formal tools should not be invoked directly from study directories, and runs should not write into this tree.

## Promotion into primary evidence

A study receives primary evidence standing only when all of these conditions are met:

1. The research question, method, result, assumptions, and falsifier are stated clearly.
2. The source and structured inputs have been audited for the claimed result.
3. Invalid, duplicate, copied, and runtime-only material has been removed or explicitly retained for a scientific reason.
4. The result directly supports a retained theory claim, boundary, or reviewer need.
5. The smallest useful source and documentation set has been selected.
6. Public paths, reviewer selectors, evidence identity, and claim ceilings have been updated together.

Until that gate is complete, this corpus remains supplementary research rather than accepted primary evidence.
