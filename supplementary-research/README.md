# Supplementary Research

## Deprecated experiments

This entire directory is deprecated. It preserves experiments that were tried,
failed methods and exploratory material for historical inspection. There is no
active repair, expansion or promotion program for these studies. They are outside
current library, kernel and primary-research acceptance gates and have the lowest
priority for future work.

The retained files document what was tried. Their presence, a historical passing
test or an importable crate does not make them supported implementations or current
evidence for the primary research. Known mistakes are recorded below; the obsolete
implementations are retained without rehabilitation. Historical results keep their
original source identities and exact limits.

A study is revisited only when a concrete current requirement needs a particular
artifact and the current primary artifacts cannot supply it. That decision names
the requirement, smallest useful artifact, expected evidence and acceptance test.
An isolated fixture or counterexample can be reused after review without reviving
the study or copying its automation owners.

### Known mistakes and limitations

| Area | What went wrong | Disposition |
|---|---|---|
| Independent automation implementations | Algorithm, crypto and execution-search studies reimplemented owners and carriers instead of binding the published canonical library. | Historical study code; no canonical-library or product-conformance credit. |
| Algorithm/crypto batch acceptance | `zip` dropped unreturned inputs; `Outcome::ok` could pass a nonempty batch with zero or too few comparisons. | Former all-input acceptance claims are invalid; independent vectors and other comparisons retain only their separate scope. |
| Algorithm prototype invariants | Zero-level hierarchy construction, unchecked Budget/FederatedBudget arithmetic, incomplete integer share totals, interior-mutable snapshot content and unaccounted DFS/BFS bounds. | Failed prototype contracts; these do not refute the published canonical owners. |
| Crypto construction account | Bisection was exported/unit-tested without an algorithm caller; Sampler generated fixtures rather than governing the seven algorithms. RSA-PSS was absent from that seven-algorithm subset. | The six-load-bearing-parts account is unsupported for that subset. |
| RSA DER helper | Advertised raw RSAPublicKey and SubjectPublicKeyInfo support, but only implemented the latter path. | Unsupported format claim retained as a known mistake; no parser repair planned. |
| Crypto hardware/constant-time comparisons | Several wrappers compared one result with itself or a clone; GHASH hardware validation returned literal true; the advertised bitsliced AES path used secret-indexed tables. | No hardware-realization or constant-time correspondence credit. |
| Verus KAT linkage | An algorithms primitive KAT imported modules absent from its actual crate root. | That source earns no executable KAT credit. |
| Reproducibility and quality | Declared Python dependencies omitted cryptography; five crypto corpus tests failed at import. Four supplementary native crates failed strict Clippy; three strict documentation builds had invalid links/markup. | These boundaries are unqualified; no dependency/lint/documentation rehabilitation is planned. |
| Execution-search comparisons | Self-comparisons, constant-selected properties, ignored modality, environment skips and hand-written trace comparisons did not demonstrate framework reproduction. | Invalidated mechanisms remain historical failed-method records. |
| Exploratory formal contracts | External-body assumptions and uninterpreted predicates did not establish implementation correspondence. | Written-model and specific finite results keep their original scope; no general conformance or necessity claim. |

### Relationship to current primary artifacts

Current primary Signal and RateLimit reductions have their own artifacts under
[`formal/structures/Signal/reduction/`](../formal/structures/Signal/reduction/SignalFromAuditSink.tla)
and [`formal/structures/RateLimit/reduction/`](../formal/structures/RateLimit/reduction/RateLimitFromBudget.tla),
with proofs and negative controls in those directories. Use their registered
primary profiles for current verification. Supplementary reduction history does
not require restarting the deprecated minimality study.

The primary memoization examples retain two provenance locators to the algorithm
study's `rust/tests.toml`. Those identify prior recipe/test material; they do not
establish oracle independence or current reconstruction. Preserve that provenance
and use the primary examples' actual construction and independent comparisons for
current evidence. A historical citation is not an instruction to rerun the donor.

The sections below describe the retained historical corpus and its original
limits. They do not restore active standing or create a repair queue.

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

The cryptography Rust corpus registers exactly seven algorithms: SHA-256, SHA-3-256, BLAKE3, ChaCha20, HMAC-SHA-256, HKDF-SHA-256, and PBKDF2-HMAC-SHA-256. Its intended corpus gate rejected empty groups and missing oracles, but its short-response acceptance defect did not enforce complete comparison of every input. Its declared Python requirements were also insufficient for the selected oracle imports. These gates are deprecated and receive no all-input acceptance credit. The algorithm-corpus Verus source contains 88 `external_body` boundaries and 83 uninterpreted specification functions; the cryptography Verus source contains 127 and 45, respectively. Both trees therefore receive no algorithm-conformance credit. Those boundaries preserve exploratory definitions and contracts, not machine-checked equivalence to the Rust algorithms.

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

## Historical reproduction

The existing supplementary selectors remain available for explicitly selected
historical inspection. They are outside current acceptance gates. Use the
maintained container entrypoint with the research source mounted once:

```text
run_proofs.py list --scope supplementary
run_proofs.py list --scope supplementary --area domain-corpora
run_proofs.py run --scope supplementary --area minimality --dry-run
run_proofs.py run --scope supplementary --area irreducibility
run_proofs.py run --scope supplementary --area execution-structure-search --contains candidate
```

The current supplementary selectors cover the TLA+ and TLAPS files only. Rust and Verus files are study sources rather than runner work items. Their results depend on the exact crate tests and Python oracle contracts named by each study; invalidated probes are non-executable source and receive no pass credit. The container commands and result interpretation rules are in `../docs/reproducibility.md`. Formal tools should not be invoked directly from study directories, and runs should not write into this tree.

## Reopening a selected artifact

A concrete current need must first justify revisiting the smallest useful artifact.
Reopening is lowest priority and requires its own recorded scope; there is no
standing instruction to repair or promote the full study. A selected artifact
receives primary evidence standing only when all of these conditions are met:

1. The research question, method, result, assumptions, and falsifier are stated clearly.
2. The source and structured inputs have been audited for the claimed result.
3. Invalid, duplicate, copied, and runtime-only material has been removed or explicitly retained for a scientific reason.
4. The result directly supports a retained theory claim, boundary, or reviewer need.
5. The smallest useful source and documentation set has been selected.
6. Public paths, reviewer selectors, evidence identity, and claim ceilings have been updated together.

Without that scoped decision and completed gate, the corpus remains deprecated
historical research and supplies no current primary acceptance.
