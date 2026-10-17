# Research Record

This record locates research outside the main papers: reconstructions, candidate searches, failed experiments, and studies that informed catalog revisions.

## Direct research support

The four papers own the public argument. [reference.md](reference.md) owns the working vocabulary. [formal-methods.md](formal-methods.md) maps each formal artifact to its purpose, location, limit, and reviewer selection.

The formal directory contains models, proofs, controls, executable contracts, and correspondence records for the catalog, composition, ownership, and ALK work. Its 23 implementation-refinement packages establish their written mappings. Applying them to another implementation requires a conformance argument.

## Problem-first design studies

The [mergeable shared-state case study](case-studies/mergeable-state/README.md) uses DAC to derive a problem's structural requirements and obligations before selecting the parts of a solution. It develops a reconciliation and publication design, compares mechanisms from memory management and replicated systems, and includes a finite executable exploration. The study identifies implementation requirements; it does not establish a new catalog entry or implementation conformance.

## LeanFormer reconstruction

[LeanFormer](leanformer.md) reports the early construction experiment. Its later reconstruction maps the examined mechanisms to the current catalog and records shared-state, orchestration, and ambiguous-signal issues. This is evidence for that construction.

The result used by the theory is the reconstruction summarized in the capstone and DAC papers; no claim depends on unlisted chronology or working records.

## Supplementary research

The [supplementary research](../supplementary-research/README.md) tree is deprecated. It preserves candidate searches, failed experiments, and tests that informed revisions, with their known mistakes and original evidence limits. These studies have no active repair or promotion program.

| Study family | Research question | Retention rule |
|---|---|---|
| `studies/domain-corpora/` | Can the proposed structures reconstruct systems from additional domains without hiding residual behavior? | Keep frozen inputs, mappings, counterexamples, and unique formal artifacts |
| `studies/execution-structure-search/` | Do candidate execution structures collapse into retained structures, remain distinct, or expose a missing observation model? | Keep separating traces and supported negative results |
| `studies/irreducibility/` | Which modeled invariants fail after a fused check and act is separated or a defining guard is removed? | Keep the paired model, configuration, violating trace, and exact claim for the tested seam |
| `studies/minimality/` | Can a target be reconstructed from the remaining catalog, admitted connective forms, and declared relies? | Keep valid and failed reductions, model-degeneracy findings, and the exact target and mapping |

A particular artifact is revisited only when a concrete current requirement needs it and the primary artifacts cannot supply it. That review identifies the requirement, selected artifact and acceptance test; it does not revive the study. Copied dependencies, caches, duplicate sources, and wrapper scripts are excluded from the research record.

## Revision rule

New structures, valid reductions, failed reconstructions, unexplained behavior, and stronger separating witnesses can revise the catalog. Repeating an existing example adds evidence about the same case.
