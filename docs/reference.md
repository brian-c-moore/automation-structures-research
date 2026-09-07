# Automation Structures Reference

This reference is the catalog of reusable state-machine abstractions produced by Automation Structures Research. It organizes the parts by behavioral obligation and records their contracts and conditions for composition. Use it to select the structures for a construction; the papers explain why these abstractions were selected and what evidence supports their use.

The [`automation-structures` Rust library](https://github.com/brian-c-moore/automation-structures) implements the parts under its documented executable profiles. `alk-core` is being built to compose them into an automation kernel. The catalogs record the structures found in the examined systems and retained after reduction, separation, reconstruction, and formal testing.

## Description layers

| Layer | Question | Main contents |
|---|---|---|
| Structure | What state and transition relation performs the work? | Abstraction primitives and named compositions |
| Connection | How do structures exchange authority, state, evidence, or work? | Connective forms |
| Execution | How is work ordered, enabled, observed, and completed? | Sequential, fork-join, step-graph, and stream-graph structures |
| Assurance | Who controls the behavior decisive for the obligation at this claim frame, and what can be claimed? | Claim-relative ownership, EIM placement, and ALK construction |

These layers are separate description axes. Select primitive and named-composition contracts for the work and execution contracts for how it advances. A system can use one catalog structure with several execution structures, or one execution structure for several catalog structures. An entry may offer alternative modes or carry several obligations; select only the contracts required by the construction.

State and transitions describe the mechanisms. Catalog membership requires a reusable responsibility at the chosen boundary. Connective forms can also carry state and transitions, but their catalog role supports the selected obligations without introducing independent obligation schemas. Each contract records the environment assumptions its realization must satisfy. The [introduction](introduction.md#state-and-behavior) explains this terminology.

## Structure catalog

| Structure | Role | Governing concern |
|---|---|---|
| ActuationPass | Apply a selected effect to a governed resource | Effect and resource identity at commit |
| AllocationSnapshot | Record an allocation result within capacity | Joined cost and remaining capacity |
| AuditSink | Append evidence under a predecessor relation | Content, order, and chain binding |
| BacktrackingTraversal | Explore choices with paired descent and restoration | Path validity and restoration |
| Bisection | Narrow an ordered interval by probes | Threshold containment and probe accounting |
| Budget | Admit actions under a hard capacity limit | Allocation, reservation, and pending charge |
| CompetitiveSelection | Admit ranked candidates into limited capacity | Eligibility, ordering, and exclusivity |
| ConvergenceGovernor | Permit updates while a governed measure approaches closure | Safe transition and recorded convergence relation |
| EquivalenceClass | Group values under a stated equivalence relation | Membership and representative consistency |
| FederatedBudget | Compose local budgets under a shared bound | Local admission and aggregate accounting |
| ForkJoin | Run independent branches and join their recorded results | Branch isolation and join readiness |
| PropagationPass | Apply one round of target updates from a common immutable round-start snapshot | Snapshot locality, coverage of selected targets, and the configured iteration ceiling; convergence remains a separate domain or governor concern |
| QualityHierarchy | Order alternatives by a stated quality relation | Admissible order and selection consistency |
| RateLimit | Bound admitted events in a stated window | Count, window, and admission boundary |
| Reduction | Combine a finite collection through a stated operator | Accumulator and input accounting |
| RelationshipGraph | Maintain typed relations among governed objects | Endpoint and relation validity |
| ResourceRegistry | Bind resource identifiers to governed records | Identity, registration, and lifecycle state |
| Sampler | Select observations under a stated sampling rule | Index and sample accounting |
| Sequential | Execute one governed step after another | Order and completion state |
| Signal | Record and deliver a named condition transition | Signal identity and delivery state |
| StepGraph | Enable steps from predecessor completion | Dependency readiness and monotonic state |
| StreamGraph | Move records through connected processing stages | Queue counts, backpressure, fan-out, and profile-specific record identity |
| TraversalEngine | Advance through a governed search or visit relation | Frontier, accepted visits, and remaining-budget state |

The formal location, proof purpose, known limits, and reviewer selector for each structure are listed in [formal-methods.md](formal-methods.md).

The catalog count of 23 contains nineteen primitive and named-composition contracts plus four execution contracts. A construction selects from the two axes separately and instantiates only the contracts and modes it uses. The exact `Budget` contract uses three usage ledgers and preserves `allocated + reserved + pending_eviction <= capacity`; [formal-methods.md](formal-methods.md) points to that model and its selected implementation refinement.

## Connective forms

A connective form is a recurring relation that joins structures without adding an independent governance obligation. It is more than a language feature or data type, and less than a full execution structure.

| Form | Construction role | Obligation-bearing neighbor |
|---|---|---|
| Projection | Derives a read or view from existing state | A materialized view with a freshness claim |
| Cursor | Retains and advances a consumer position | A consumer with delivery or replay guarantees |
| Accumulator | Carries a partial result between steps | A checkpointed or integrity-protected partial result |
| Marker | Retains a reference value for a later predicate | A governed epoch, lease, or checkpoint |
| Counter | Retains a monotone count used as progress identity or a gate | A consensus term or exactly-once sequence |
| Buffer | Retains pending items under a supplied removal discipline | A queue governed by a capacity limit or delivery policy |
| OrderingPass | Arranges a finite collection before later work consumes it | An ordering service with a stability or fairness guarantee |

A role enters this catalog when ordinary host state or logic can represent it without another catalog entry, no independent governance property is claimed for it, its domain-neutral description recurs across the examined domains, and naming it removes residue from a retained recipe or reduction. If a construction claims a separately violable property for one occurrence, that occurrence crosses the obligation boundary and must name the structure or runtime contract that supplies the property.

## Named compositions

Named compositions are recurring construction recipes. Each recipe names its component structures, connective forms, shared state, primary obligation schemas, contributing clauses, assumptions, proof bindings, evidence, and residuals. A system instantiation later assigns the subject, decisive behavior, owner, and failure model.

| Composition | Current recipe | Intended result |
|---|---|---|
| AllocationSnapshot | `ResourceRegistry<Node, Cost> + Budget<Cost>` | Accepted membership aligned with charged cost and remaining capacity |
| FederatedBudget | Master `Budget` plus one `Budget` per subpool | Master and subpool allocations within their declared ledgers and ceilings |
| Bisection | `Budget<Probes>` plus converging cursors | Probe ceiling and the tested halving or monotonic-progress relation |
| EquivalenceClass | Parent registry, rank registry, and operation budget | Tested equivalence, path, and rank obligations |
| RateLimit | `Budget<Operations>` with clock-driven window reset | Admission within the modeled window ceiling; operational rate limiting requires a positive window duration |
| Reduction | `AuditSink<Element>` with the chain operation instantiated as left-fold combine | Agreement between the ordered consumed prefix and carried aggregate |
| RelationshipGraph | Registry of flattened edges plus adjacency projections | Deterministic edge storage and consistent adjacency in the current irreflexive profile |
| Sampler | `Budget<Samples> + ActuationPass<Item, Probability>` | Selection from the supported set within a sample budget |
| Signal | `AuditSink<Value>` plus predicate-filtered cursor consumers | Declared notifications tied to recorded changes and consumer positions |
| TraversalEngine | `RelationshipGraph + Budget<NodeCost>` | Visit and acceptance under a cost budget over the tested topology |

Composition never grants a stronger claim by name alone. The builder must discharge the component obligations, preserve the declared connective semantics, close shared-transition duties, assign owners, and avoid circular rely credit.

The RateLimit model admits zero duration as a degenerate parameter: every acquisition resets the
recorded count, so the count bound holds while throttling is absent. A rate-limiting construction
selects a positive duration and states the clock-delivery assumptions separately.

## Execution structures

| Structure | Ordering model | Observation boundary | Main limit |
|---|---|---|---|
| Sequential | One enabled step commits at a time in a recorded order | Step start, commit, and completion | Does not express independent branch completion |
| Fork-join | Independent branches execute before a join condition | Branch lifecycle and join | Does not by itself supply arbitrary dependency or stream semantics |
| Step graph | Steps become enabled from predecessor completion | Node state and dependency edges | Progress still requires an inhabited rank or another stated liveness argument |
| Stream graph | Records move across connected stages | Record, edge, stage, and fan-out events | Delivery, capacity, retry, and ordering claims depend on the selected profile |

The retained refinement results are `Sequential -> StepGraph`, `ForkJoin -> StepGraph`, and `StepGraph -> StreamGraph`, under their written mappings and observation choices. The separation witnesses show finite traces that distinguish selected structures. Neither result establishes a complete ordering of every possible execution model.

## Common semantic record

The semantic record separates the reusable contract from the system claim.

| Stage | Field | Required content |
|---|---|---|
| Structure contract | Obligation schema | Reusable responsibility, available modes, parameters, and assumptions |
| Structure contract | Contract clauses | Exact formulas, temporal form, engineering concern, proof roots, and derivation status |
| Structure contract | State and actions | Variables, observations, and system or environment transitions used by the clauses |
| Obligation instance | Claim frame | Subject, obligation, mode, scope, observation boundary, authority boundary, claimant, failure model, abstraction, lifecycle phase, and property form |
| Obligation instance | Decisive behavior | Every action, omission, trace choice, evidence step, or custody step that can decide the obligation |
| Obligation instance | Rely and failure model | Conditions supplied elsewhere and failures the claim must survive |
| Ownership result | Eligible boundary | Authority or named protocol that covers the decisive behavior at the declared frame |
| Ownership result | Canonical owner | One selected eligible principal or named protocol, or an explicit unowned result |
| Ownership result | Accountability and delegation | Technical accountability matching the canonical owner, delegated work, transferred authority, and any independently controlled behavior outside the boundary |
| Claim result | Owned claim | Prevention, detection, or recovery guarantee issued by the enforcement owner |
| Claim result | Assurance profile | Exact A0-A5 propositions and mechanisms supporting a claimant's confidence in another owner's obligation |
| Claim result | Evidence and ceiling | Evidence path, custody, verifier, timing, and strongest handled failure class |
| Review record | Residual and falsifier | Relevant behavior left outside the construction and a condition or trace that defeats the claim |

This record prevents a structure name from standing in for an argument. Two systems that use the same named structure may support different guarantees because their owners, placement, execution structure, evidence path, failure model, or recovery behavior differ.

## Claim-relative ownership

[Claim-Relative Ownership and Assurance](claim-relative-ownership.md) defines the common ownership
model. Ownership is a partial function over complete claim frames: one canonical owner or none at a
fixed perspective and abstraction. Related algorithmic, component, protocol, system, and
organizational frames may have different owners. Refinement and composition connect their
obligations without turning them into shared ownership.

Delegated work always creates a trust boundary and an explicit rely. Ownership and technical
accountability remain with the canonical owner while its mechanism still covers every
obligation-decisive outcome. If complete decisive authority transfers, ownership and accountability
transfer. If authority is split and no named protocol covers the end-to-end obligation, it is
unowned and the parties retain only their narrower guarantees and assurances.

The claim-specific TCB contains every mechanism whose correct behavior the owner's guarantee needs.
The owner's authority base is a subset of that TCB; independently controlled members are external
relies and require assurance. TCB membership never creates co-ownership.

## EIM and ALK

The Execution Integrity Model maps an intended claim frame to the surface where the obligation can fail, eligible controlling boundaries, one canonical owner or an unowned result, every delegation trust boundary, the owner's guarantee, the claimant's assurance profile, the evidence path, and the failure ceiling. A local check, receipt, signature, or later query can support a narrower guarantee or assurance class; it does not restore ownership of an independently controlled outcome.

The Automation-Layer Kernel is the claim-relative construction used when selected obligation schemas are instantiated across those surfaces. The intended construction requires exact schema-to-clause bindings, selected modes, mediated governed paths, fail-safe admission, authority-derived ownership and delegation, sound composition, evidence coupled to decisive behavior, and explicit residuals. The current formal model checks supplied labels and generic semantics; it does not establish exact catalog-predicate instantiation, real-authority binding, or owner-issued claims.

The conditional ALK theorem derives its represented result under supplied owner, controller, provider, evidence, failure, and TCB premises. It does not derive enforcement ownership from real authority, bind each result to an explicit issuer, or establish that ALK is necessary, unique, complete, or suitable for every automated system. The four profile models instantiate finite local, modular, delegated, and distributed configurations from those inputs. `ALK-SPEC-1` is the versioned reference state machine and API artifact for operational requests, responses, state changes, retry behavior, and evidence events; it does not serve as the static claim certificate.

## Builder record

For each intended claim, record the selected structure and execution contracts, modes, primary obligation schemas, exact clauses, connective forms, component mapping, claim boundary, decisive behavior, enforcement owner, claimant, delegation boundary, remaining local guarantees, assurance profile, relies, evidence path, recovery behavior, failure ceiling, residuals, and falsifiers. Then use [formal-methods.md](formal-methods.md) to locate the existing formal evidence and [reproducibility.md](reproducibility.md) to select the smallest relevant proof run.
