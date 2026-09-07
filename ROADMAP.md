# Roadmap

Automation Structures Research has produced a catalog of reusable state-machine abstractions,
organized around behavioral obligations, with explicit contracts and conditions for composition.
The `automation-structures` Rust library implements the parts; `alk-core` is the automation kernel
being built from them. This file records what exists today and what remains to be built and checked.

The immediate aim is a GitHub release of the research and its evidence. Further implementation
and examples test the choice of abstractions and their composition. A planned blog will explain
how to build with the structures and develop the theory into a course or book.

## Current state

[Claim-Relative Ownership and Assurance](docs/claim-relative-ownership.md) defines the claim frame,
coverage eligibility, canonical ownership, technical accountability, delegation, transfer,
owner-issued guarantees, claimant assurance, and claim-specific trusted computing bases. Its formal
package under `formal/assurance/ownership/` types those relations, checks a finite multiscale
witness, discharges the proof consequences, and runs controls for shared ownership, non-owner
issuance, assurance credited as ownership, and delegated work mistaken for transferred authority.

Accountability is intrinsic to ownership at the same claim frame. Only the actual owner can issue
the obligation's guarantee. A party that no longer owns it can maintain assurance about that outcome
and may still own other, separately framed obligations. The formal definitions express these
relationships through ownership, accountability, guarantee issuance, and assurance records.

The construction registry at `formal/construction/alk/ALK_REGISTRY.json` binds 36 obligation schemas
to 69 clause occurrences across the 23 catalog entries. Each schema names its selected mode and
separates primary, contributing, supporting, derived, and selected-policy clauses. Each clause names
its predicate, proof roots, assumption set, temporal form, engineering concern, qualifiers, and
outcomes. Generation and static checks reject a missing, wrong, duplicate, or cross-mode binding.

Every cataloged structure has an evidence chain from a TLA+ specification through a TLAPS proof to a
Verus implementation proof, with negative controls for the written clauses. The Rust implementation
is published separately as
[`automation-structures` 0.2.3](https://crates.io/crates/automation-structures). The verifier image
fetches that exact archive by checksum and runs the implementation checks against it.

The [reference](docs/reference.md) distinguishes reusable structure contracts from their selected
executable profiles. Evidence for one profile does not establish every implementation of its schema;
the research's implementation claims identify the exact archive and contract they cover.

The [Formal Examples](formal/examples/README.md) already demonstrate structural reuse across
domains. LOD and route selection invoke the same `rooted_frontier` composition, with domain-specific
policies and controls for each shared ordering edge. Ten dynamic-programming algorithms invoke one
Memoization composition. These are existing constructive results to explain and build upon.

The selected ALK claim package is implemented. `formal/construction/alk/tla/ALKClaimInstantiation*` and
`ALKClaimActionBinding*` bind the `AS-BUD-CAP` and `EX-SEQ-SERIAL` pair to actual Budget and
Sequential predicates and actions. The action-partition proof retains the original carrier
transition relation. `ALKClaimAuthority*` derives coverage and ownership from modeled controller
gates and the canonical-owner designation, and checks transfer, split authority, protocol decisions,
and issuance against actual execution. This closed model assumes authentic controller identity
and excludes external bypasses; it is not an implementation authority certificate.

`ALKClaimProgress*`, `ALKClaimRelational*`, and `ALKClaimEvidence*` add distinct finite boundaries:
fair completion of the two-step Sequential carrier; matched histories of two carriers under coupled
choices; and capture, custody, detection, and snapshot restoration for one persistent Budget fault.
Their controls distinguish safety from progress, individual contracts from a paired-trace claim,
and attribution or observation from continued truth. Diagnostic bounds use logical clock ticks
under explicit clock and storage premises. These results do not certify all catalog obligations,
the deployment profiles, arbitrary trace equivalence, or real-time recovery.

The shared evidence interface binds each A0-A5 record to its proposition, frame, producer, verifier,
claimant, observation, custody, mechanism-owned claim, and semantic premise. The diagnostic witness
supplies those premises from its actual actions and derives its authority from the diagnostic gates.

A static certificate carries the selected catalog result alongside three separate reference-state
claims. The profile adapter and read-only reference view preserve complete frames, revisions,
authority, issuer, recipient, evidence, assurance, relies, TCB, and residuals. The seven supported
profile/mode configurations retain their existing state counts. A separate unsupported-bound case
receives unavailable claims. The [ALK Claims guide](docs/alk-claims.md) records the exact
scope and the remaining catalog-to-profile refinement and implementation work.

## Reading and reviewing the research

The [README reading path](README.md#start-here) starts with Budget, follows the shared LOD/OSPF
construction, and then leads into the theory and its evidence. The
[introduction](docs/introduction.md#relationship-to-prior-art) describes the project's aim as a
synthesis and relates it to component composition, contracts, and control analysis.
[CONTRIBUTING.md](CONTRIBUTING.md) welcomes questions about explanations and attempted constructions
alongside errors and counterexamples.

A research release requires complete primary evidence coverage and independent claim/prose review.
Each result retains its checked source identity, and crate bindings identify the actual artifacts
reviewed. The verification section below explains how unchanged-input evidence is carried forward.

## Implementation and further research

`alk-core` is being built as an automation kernel composed of reusable state-machine
implementations, organized around behavioral obligations, with explicit contracts and conditions
for composition. It is the ALK implementation target, in early development outside this repository.

The intended kernel brings the catalog together through the published `automation-structures`
library. The same parts build the kernel's execution machinery and the components developers
assemble into flows. Each flow selects the structures and execution contracts it needs;
hierarchical components lower into one admitted execution plan under one kernel authority.
Full catalog integration and implementation conformance remain open.

The `AuditSinkSummary`, `ReductionSummary` and `SignalSummary` research profiles under
`formal/structures/*/refinement/` now describe summary observations with a logical audit-history
witness. Parametric proofs map them to the existing canonical models; finite controls challenge
count, carry, latest value, capacity, source order and notification acknowledgement. They establish
no compact Rust implementation or retained runtime audit evidence. The published full-history
contracts and catalog classifications are unchanged; typed storage and consumer conformance remain
implementation work. The [formal index](formal/README.md) gives the focused selector and limits.

The target kernel owns the covered execution, resource, effect, and evidence transitions.
Existing reconstructions such as LOD/OSPF provide recipes to carry through that public
construction and execution path.

| Workstream | Next result | Evidence boundary |
|---|---|---|
| Selected NeetCode algorithm corpus | Expand the worked algorithm examples to all 87 selected NeetCode algorithms, building on the existing ten Memoization instances and reusing shared compositions wherever their contracts fit. | Track each selected algorithm's construction, input contract, independent reference, controls, and accepted evidence. Completion means all 87 selected entries have worked examples with explicit results and limits. |
| Selected cryptographic algorithm corpus | Develop worked structural constructions for all 15 selected cryptographic algorithms. | Track each selected algorithm's construction, applicable reference or authoritative test vectors, controls, and accepted evidence. Completion means all 15 selected entries have worked examples; each records the functional, structural, and security properties its evidence covers. |
| [Problem-first DAC: mergeable shared state](docs/case-studies/mergeable-state/README.md) | Freeze the mechanical assembly recipe, then build a bounded architecture PoC covering obligations O1-O16 through declared minimal profiles. Assemble canonical structures and compositions with explicit domain parameters and runtime providers. Full document merging and primitive minimality are outside this target. | The writeup and finite Python exploration are available; structural assembly remains planned. Acceptance requires successful paths and discriminating controls showing that the actual canonical components and their connections enforce each obligation. Unsupported behavior remains an explicit gap; handwritten replacement machinery does not earn assembly credit. |
| Implementation conformance | Align `alk-core` with the accepted library release and map executable state, actions, identity, permissions, failures, and evidence to the research contracts. | A research certificate or component proof does not grant whole-engine implementation credit. |
| Reuse through the engine | Demonstrate existing structural recipes through public component, admission, and execution APIs, then extend to other applications as their contracts are supported. | Record which machinery is reused, what domain code remains, and where bespoke structural mechanisms are still needed. |
| Performance and composition economy | Measure the accepted engine on named workloads, including memory, CPU, latency, evidence costs, and authored glue. | Historical PoC results motivate the design; performance and usability claims attach to the measured implementation and configuration. |
| Further claim instances | Add a catalog/profile refinement, failure model, progress result, or TCB-minimality argument when a concrete claim needs it. | The current certificate retains unsupported relations as explicit residuals. |
| Learning from related work | Use selected ideas from contract composition, security authority, STPA, deterministic coordination, and resource-rights reasoning to examine concrete constructions. | A proposed comparison is not a new accepted claim or catalog entry. Existing evidence and residuals determine what work is needed. |

The corpus targets are the full selected sets: 87 NeetCode algorithms and 15 cryptographic
algorithms. Coverage should be recorded by named entry so that planned, implemented, and accepted
examples remain distinguishable as the work progresses.

These are continuing implementation and research directions. The GitHub research release does not
depend on completing the engine or expanding the catalog to cover every proposed application.

## Teaching the theory

A planned blog will develop the explanation in enough detail to serve as a course or book. The
repository will provide the definitions, executable examples, evidence, and revision history that
the lessons refer to. Published lessons should identify the repository version they explain.

The proposed progression is:

1. Attaching an obligation to a system and identifying the structural boundary.
2. Understanding one structure through a concrete failure and its prevention.
3. Ownership, intrinsic accountability, guarantees, delegation, and assurance.
4. Composing structures and accounting for the obligations at their joins.
5. Following the shared LOD/OSPF construction across two domains.
6. Building components and admitted execution with `alk-core` as that implementation becomes available.

The CAGED analogy explains reusable form and domain content; the construction analogy explains
obligations, connections, and the conditions under which an assembly holds. Reader questions and
attempted constructions will help identify where the teaching sequence or underlying account needs
improvement. The full teaching material can grow after the GitHub release.

## Verification

Focused selections cover changed proof inputs. A complete run records the checked source
fingerprint and exact selection. The
[Reproducibility Guide](docs/reproducibility.md) has the build and run commands, and
[formal-methods.md](docs/formal-methods.md) records each artifact's purpose, location, limit, and
reviewer selector. Independent review must account for each result's source identity. Earlier
results may be retained for unchanged inputs when an exact source comparison shows what changed;
affected inputs require fresh focused checks.

## Revising this roadmap

The catalogs and this list stay open to revision. A counterexample, an unmapped residual, a valid
reduction, or a failed reconstruction can reorder or remove an item.
[CONTRIBUTING.md](CONTRIBUTING.md) states the standard for a material change.
