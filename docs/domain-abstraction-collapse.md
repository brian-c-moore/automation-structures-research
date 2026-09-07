# Domain Abstraction Collapse

## A Practitioner Method for Identifying Governed Automation Structures

---

## Abstract

Domain Abstraction Collapse (DAC) explains how the reusable state-machine abstractions in the Automation Structures catalog were identified beneath domain vocabulary. It first records how each system in a declared survey works in its own terms. It then removes domain content to compare the remaining behavior and responsibilities. A proposed shared construction must reconstruct each source system. Any behavior it cannot account for is recorded as a residual that can change the mapping or catalog.

A visibility buffer, a pod scheduler, and a market matcher illustrate the method: each scores candidates for seats and commits an allocation. The shared structure defines an obligation schema; a concrete design supplies its subject, scope, and domain parameters. Runtime assumptions and connective forms remain explicit in the recipe.

A survey of twelve engineering domains produced the initial catalog. An algorithm corpus added entries, and later reduction work reclassified others. Formal artifacts test the stated contracts; executable examples test reconstructions. The early [LeanFormer](leanformer.md) experiment tested whether the method could produce an implementable design in an unfamiliar domain. Section 9 records the evidence for these results.

---

## 1. Introduction

### 1.1 Patterns Hidden by Vocabulary

Fred Brooks distinguished essential complexity from accidental complexity [1]. DAC treats domain vocabulary as one source of accidental complexity: two systems can perform the same kind of governed work while their communities describe that work with unrelated terms.

Domain vocabulary can make useful comparisons harder to see. A structural description exposes state, transitions, and responsibilities in terms that can be compared across fields. It can also state a new system's requirements before a domain-specific solution is chosen.

In an Entity Component System (ECS), an entity is an identifier, a component is a typed record, and a system queries component combinations before applying work. This description exposes a database-like structure and makes storage, query planning, schema change, and access-control techniques available for comparison. Data-oriented design already uses the ECS/database comparison.

The same kind of recurrence appeared across the engineering systems examined for this research. After domain nouns were removed, their architectures often admitted shorter descriptions in terms of resource bounds, selection, propagation, convergence, mutation, and evidence.

A catalog entry is useful when a builder can recognize its construction, locate its responsibility, and reuse an implementation or proof pattern. Familiarity across domains supports that practical aim.

### 1.2 The Methodology: Domain Abstraction Collapse

DAC asks a second question after a domain explains how its system works: what state changes, resource limits, ownership decisions, and guarantees remain after the local names are removed? The repeatable method has five steps.

1. Freeze the survey. Name the systems, abstractions, source material, and observations included in the analysis.
2. Describe the work in its own terms. Record state, transitions, actors, commits, assumptions, failure cases, and declared obligations.
3. Strip domain content. Replace local nouns with structural roles while preserving behavior, interference, ordering, and the properties the system promises.
4. Classify and collapse. Separate runtime givens, candidates that define obligation schemas, connective forms, and domain parameters; merge candidates only when a shared construction preserves the recorded behavior and responsibility.
5. Reconstruct and test. Give each surveyed system a recipe, check representative realizations, and retain any unexplained residual as a revision input.

At step 4, descriptions can collapse into one construction with different domain parameters. Step 5 tests whether that construction preserves each source system's behavior and obligation placement.

The resulting record and recipe explain how to rebuild the system from the proposed parts. They state what each part does, how the parts connect, and what they need from the domain and runtime. They identify the governed commits and who controls the behavior decisive for each obligation. Where control remains external, the record names the assurance mechanisms and evidence available to the party relying on that behavior.

DAC identifies the reusable responsibilities and how they compose. Choosing how work is triggered and how admitted work progresses are separate design decisions. The Execution Integrity Model (EIM) evaluates ownership and assurance after the selected contracts are instantiated in a system.

### 1.3 Problem-First Construction and Reconstruction

DAC can begin with an existing system or a problem that has no implementation. At the chosen system boundary, first describe what must happen, what must never happen, and which failures the system must withstand. Write this as a problem record, with the constraints and required evidence, before choosing catalog entries.

The structural design record then explains how the selected parts meet those requirements. It identifies their connections, the shape and execution of the work, and ownership or assurance for each obligation. It must also state what the design assumes of the runtime and what the domain supplies.

Two checks follow. Design adequacy asks whether the design meets the problem's obligations under its assumptions. Implementation conformance asks whether the built artifact preserves the design's behavior, including its states, transitions, commits, and guarantees. Reconstructing an existing system produces the same records in reverse for comparison with the original problem. DAC organizes these checks; it does not provide a general decision procedure for arbitrary problem satisfaction.

LeanFormer is an implemented problem-first instance: its training problems were stripped before the structural design was implemented. Section 5 summarizes the experiment, and [leanformer.md](leanformer.md) carries the full report.

The [mergeable shared-state case study](case-studies/mergeable-state/README.md) uses the same method to develop a solution to independently edited objects whose relationships can break during reconciliation. It derives the obligations before selecting structures, considers mechanisms from memory management and replicated systems, and exercises a finite tree-editing design. Its result is a structural design with explicit implementation requirements; primitive reduction is a separate question.

### 1.4 Abstraction Primitives: Why the Decomposition Stops Here

Decomposition stops at a useful automation structure when the remaining shape defines a reusable responsibility whose success or failure matters to the system. Failure may be an unsafe action, missing progress, a bad relation across a trace, or missing evidence. For safety, splitting check from commit exposes one decisive placement question: which authority can constrain the falsifying transition?

This gives the lower boundary. Arithmetic, iteration, data representation, and domain functions can participate in an automated system without defining a governance responsibility of their own. Resource ceilings, exclusive allocation, progress rules, and audit continuity cross the boundary when the system accepts responsibility for them. Above these structures is the content boundary: resource types, policies, scores, effects, and workload data supplied by the domain.

Automation begins when a built system executes work under a stated obligation without a human enforcing each step. The design then needs an enforcement owner for all behavior that can decide that obligation, or an explicit trust-boundary and assurance record where authority remains external. Invocation can still come from a person, event, schedule, or another system; the trigger is separate from the structure that defines the reusable obligation schema.

A reusable shape between those boundaries is an automation structure. An abstraction primitive is the lowest reusable semantic unit at the selected abstraction whose obligation-bearing behavior is not supplied by a tested composition of other entries over the pinned connective vocabulary. Atomicity is relative to the chosen decomposition: a primitive may need several clauses, offer alternative modes, or expose more than one distinct obligation. A named composition remains useful after a reduction is found, and its recipe records which components supply each responsibility. Catalog membership follows the current evidence rather than a fixed count.

The decomposition must also remain useful to a builder. Instructions and logic gates can express the behavior, but a recipe at that level no longer explains which part is responsible for keeping a promise. A useful recipe must expose the behavior decisive for the obligation, its owner, and the conditions of its guarantee. DAC stops where the parts are implementable and those responsibilities remain visible.

### 1.5 Related Work and Intellectual Lineage

The following work provides related methods and construction concepts.

Brooks' essential/accidental complexity distinction [1] supplies one antecedent. DAC treats local vocabulary as a source of accidental complexity in conceptual framing.

Pattern languages, including Alexander's work in architecture [a-1] and Gamma et al.'s software design patterns [a-2], identify recurring motifs and give them shared names. DAC adds an explicit obligation test, a reconstruction step, and a residual record, and its catalog stays tied to the survey that produced it.

Information hiding (Parnas) [a-3] and abstract data types (Liskov) [a-4] articulated the principle that interfaces should hide implementation details that vary across cases. The primitives here can be read as abstract data types whose interfaces are governance invariants and whose implementations vary per domain.

Coordination languages (Linda [a-5], Reo) and process algebras (CSP [a-6], the actor model [a-7], pi-calculus) give domain-independent accounts of concurrent and distributed computation. Several DAC entries have neighboring forms in that work. DAC keeps a builder-facing vocabulary and tracks the reusable responsibility defined by each construction.

Wing's work on computational thinking [a-8] argues that recognizing the computational structure underneath domain problems is a general intellectual skill. DAC is a specific procedure for doing that for a class of resource-governed execution systems.

Workflow management formalisms, including van der Aalst's workflow patterns [a-9], catalog control-flow patterns across process systems. Section 7 records overlap found when the DAC survey examined graph workloads outside workflow products.

Algorithmic skeletons [a-10] and the parallel-pattern catalogs that followed [a-11, a-12] name recurring constructions such as map, reduce, scan, pipeline, farm, fork-join, and stencil. DAC's control entries overlap with part of that vocabulary. The surveyed systems also required explicit resource, convergence, and evidence obligations, which account for other entries in the current catalog.

Kleppmann and Alvaro compare convergence approaches from four computer-science communities [a-13]. They identify coordination requirements for limited resources such as balances and exclusive seats. DAC maps these to Budget and CompetitiveSelection, while retaining the domain rules needed for each system. The survey also illustrates why a shared vocabulary can help compare neighboring research.

Warth, Ingalls, and van Hardenberg report convergent replicas whose merged writes break linked-list and tree invariants [a-16]. They propose defining merge behavior through abstract-type operations. DAC and EIM interpret the case as a check-act and placement problem: a merge cannot enforce a constraint it neither represents nor controls at commit.

DAC identifies candidate responsibilities and the behavior that decides them. EIM then assigns ownership and assurance at a declared claim frame. [Claim-Relative Ownership and Assurance](claim-relative-ownership.md) defines that relation, including delegation, authority transfer, and unowned obligations.

### 1.6 The Turing Tarpit Question

The Turing Tarpit objection is straightforward: sufficiently low-level decomposition makes unrelated systems look alike while producing little construction value.

The response is empirical. The initial task was to design one execution kernel for ETL, SOAR, and configuration-management workloads. Further domain reviews were added as adjacent systems raised new construction questions. Some candidates recurred, others split, and later corpora added or reclassified entries.

Rendering entered the survey through orchestration. Comparing level-of-detail selection with priority-driven route computation exposed budgeted traversal and selection questions absent from the initial automation domains. OSPF itself remains a link-state protocol with shortest-path, topology, convergence, and failure semantics that this comparison does not reduce. Later surveyed systems either received a faithful recipe or left a recorded residual.

A useful recipe must be compact enough to build while exposing the responsibilities that matter. The recorded mappings test that criterion; revisions and residuals identify where it failed.

### 1.7 Contributions

The paper makes four contributions:

1. A repeatable method for deriving buildable, domain-neutral structures from a declared survey and revising them from residuals.
2. Working definitions for the obligation boundary, content boundary, automation structure, abstraction primitive, named composition, connective form, and runtime given.
3. The catalog and mapping record produced by applying the method to the systems and corpora described here, with formal questions attached to the catalog entries.
4. The [LeanFormer](leanformer.md) feasibility experiment, which decomposed and reconstructed an ML training system through the sixteen hypothesized entries before the formal research settled the catalog.

---

## 2. The Surveyed Systems and Resulting Catalog

### 2.1 The Domains Examined

The survey grew from execution-framework design. SOAR was the starting point; subsequent design questions brought in the other eleven domains.

| # | Domain | Entry Point |
|---|--------|-------------|
| 1 | Security Orchestration (SOAR) | Original motivation: frustration with existing SOAR platforms |
| 2 | CI/CD Pipelines | Mapped to a DAG-workload recipe also used for surveyed SOAR playbooks |
| 3 | ETL / Data Pipelines | Recognized as DAG workloads with different I/O stages |
| 4 | Configuration Management | Recognized as declarative state convergence |
| 5 | Container Orchestration | Recognized as budget-constrained resource allocation |
| 6 | Real-Time Rendering | First GPU domain: tested whether primitives held under real-time constraints |
| 7 | Physics Simulation | Multi-stage pipeline decomposed to selection plus propagation |
| 8 | Audio Spatialization | Budget-constrained propagation over spatial graph |
| 9 | Network Replication | Spatial budget allocation in bandwidth units |
| 10 | Economic Simulation | Competitive selection plus propagation plus transactions |
| 11 | Distributed Consensus | Component-level study of election, replication, and commit in Raft; no protocol-level reduction is claimed |
| 12 | Machine Learning | Early construction experiment in an unfamiliar domain |

### 2.2 The Abstraction Primitive Set

Abstraction collapse across the recorded domains produced the initial catalog. The tables below are a paper-level view of the primitives' responsibilities; [reference.md](reference.md) records current membership and classification, because formal checks can promote, split, reduce, or reclassify an entry.

Data primitives (how data is structured and related):

| Primitive | Current obligation-bearing role |
|-----------|----------------------|
| `Budget<U>` | A three-ledger pool preserving `allocated + reserved + pending_eviction <= capacity` |
| QualityHierarchy | A tree of representations at multiple fidelity levels |
| `ResourceRegistry<K, V>` | A unique key to value mapping |

Control primitives (how computation is organized and orchestrated):

| Primitive | Current obligation-bearing role |
|-----------|----------------------|
| CompetitiveSelection | Allocate candidates to seats under a scoring function (three modes: hard, soft, ranked) |
| ActuationPass | Apply a side-effecting operation to a set of items |
| PropagationPass | Snapshot-isolated graph updates with a declared round limit; convergence stays external |

Coordination primitives (how the system observes and governs itself):

| Primitive | Current obligation-bearing role |
|-----------|----------------------|
| ConvergenceGovernor | Detect fixed-point convergence and govern iteration, via a phase machine with a no-skip property |
| AuditSink | A hash-chained append-only log of mutations |

Algorithmic primitives (how search state is advanced and restored):

| Primitive | Current obligation-bearing role |
|-----------|----------------------|
| BacktrackingTraversal | Traverse a finite decision tree while pairing each mutation with exact undo and recording reached leaves truthfully |

Minimality checks reclassified some entries as named compositions. For example, `Signal<T>` reduces to AuditSink plus a predicate-filtered pull consumer, and RateLimit to `Budget<Operations>` plus a clock-driven reset. The names remain useful; their recipes identify which parts supply the obligations.

A primitive is defined by its interface and obligation schema. The domain supplies parameters: thresholds for ConvergenceGovernor, a scoring function for CompetitiveSelection, or an operator for Reduction.

Some compositions require atomic operations, including a destination write or an exchange between two Budgets. The TLA+ models represent each as one transition; a runtime must supply the corresponding transaction or synchronization mechanism. Atomicity is a runtime given. The optimistic STM case study in [Formal Examples](../formal/examples/README.md) reconstructs a finite transaction manager from catalog parts while retaining one atomic epoch word as its runtime assumption.

### 2.3 The Structural Interface

The structural interface is language-neutral:

| Field | Required meaning |
|---|---|
| Input | domain content admitted by the construction |
| Governed state | state relevant to fulfilling or violating the instantiated obligation |
| Transition | enabling condition, commit point, and resulting state |
| Output | value or effect exposed after the governed transition |
| Obligation | property preserved at the commit or over the accepted trace |
| Relies | runtime and environmental conditions under which the guarantee is issued |
| Guarantee ceiling | the strongest claim supported when the relies hold |

Entry-specific specifications define those fields. Composition still requires rely/guarantee and ownership analysis at the seams. No programming-language interface is part of the theory.

### 2.4 Connective Forms and Construction Accounting

DAC separates four construction strata because a useful recipe must say which responsibilities come from governed structures and which material merely joins them. Hiding that distinction lets an ordinary queue, cursor, or projection absorb an unstated obligation and makes the claim impossible to review.

| Stratum | Supplied by | Required record |
|---|---|---|
| Runtime rely | execution environment or external provider | provider, behavior, failure condition, and trust boundary |
| Obligation-bearing structure | primitive or named composition | state, transitions, obligation schema, contract clauses, assumptions, and proof bindings |
| Connective form | construction recipe | ordinary state or logic role and the composition that owns any required property |
| Domain parameter | application domain | policy, mathematics, scoring, encoding, effect, or value semantics |

A connective form is reusable structure or logic that helps assemble governed parts without defining an independent obligation schema. A buffer used only to retain pending work is connective state. A queue that claims a capacity ceiling, durable delivery, or freshness has crossed the obligation boundary and must name the structure or runtime contract that supplies that responsibility.

The selected vocabulary admits a connective form when all of these tests hold:

1. No independent governance property is claimed for the role.
2. Ordinary host state or logic can represent it without defining another catalog entry.
3. The description remains meaningful after domain nouns and values are removed.
4. The historical census records recurrence across more than one problem domain.
5. Naming the role removes unexplained residue from a retained recipe or reduction.

Promotion occurs when a construction assigns an independent responsibility to a connective occurrence. The promoted candidate must identify the obligation schema, its failure behavior, contract clauses, assumptions, and proof bindings. The system instantiation later supplies the subject, scope, decisive behavior, owner, and failure model. A similar name or a more elaborate implementation is insufficient.

Reduction moves in the other direction. A candidate becomes a named composition when retained structures plus the pinned connective vocabulary reproduce its behavior and obligation placement under stated relies. The result belongs to the tested target and boundary.

The retained reductions use seven connective forms:

| ID | Form | Construction role | Neighbor that defines an obligation schema |
|---|---|---|---|
| CF-001 | Projection | derives a read or view from existing state | materialized view with a freshness claim |
| CF-002 | Cursor | retains and advances a consumer position | consumer with delivery or replay guarantees |
| CF-003 | Accumulator | carries a partial result between steps | checkpointed or integrity-protected partial result |
| CF-004 | Marker | retains a reference value for a later predicate | governed epoch, lease, or checkpoint |
| CF-005 | Counter | retains a monotone count used as progress identity or a gate | consensus term or exactly-once sequence |
| CF-006 | Buffer | retains pending items under a supplied removal discipline | queue governed by a capacity limit or delivery policy |
| CF-007 | OrderingPass | arranges a finite collection before later work consumes it | ordering service with a stability or fairness guarantee |

Each reconstruction records enough material to expose hidden assumptions:

| Record field | Review question |
|---|---|
| Obligation-bearing parts | Which primitives or named compositions supply the required schemas? |
| Connective forms | Which projections, cursors, accumulators, markers, counters, buffers, or ordering passes join them? |
| Domain parameters | Which policies, functions, values, and effects remain application supplied? |
| Runtime relies | Which providers supply atomicity, persistence, time, scheduling, randomness, or transport? |
| Residual behavior | Which source behavior remains outside the recipe or current evidence? |

Two boundary examples show why the accounting matters. A plain Buffer records pending items and a removal rule; a capacity-governed queue also needs a Budget or another named capacity contract. A Projection computes a view from existing state; a materialized view that claims staleness control needs a freshness obligation with an owner and decisive behavior. The code may look similar. The advertised responsibility changes the classification.

G v1.1 pins the connective vocabulary so reductions and recipes have a stable basis: the seven forms are the ones retained by this research, and residual evidence, a faithful reduction, or a newly claimed independent obligation revises the classification. The engineer-facing definitions and catalog are in [reference.md](reference.md).

### 2.5 Domain Patterns Reduced to Primitive Compositions

The tables record structural mappings from the surveyed systems. Section 9 states their evidence levels. The implemented subset in [Formal Examples](../formal/examples/README.md) also has reference comparisons and controls; the remaining rows are mappings awaiting executable evidence.

Real-Time Rendering:

| Domain Abstraction | What It Is |
|---|---|
| Visibility buffer | CompetitiveSelection (hard): triangles compete for pixel ownership, depth is the scoring function |
| Deferred shading | ActuationPass over the AllocationSnapshot from the visibility CompetitiveSelection |
| Level of detail (LOD) | QualityHierarchy + TraversalEngine + CompetitiveSelection + AllocationSnapshot under `Budget<Bytes>` |
| Frustum culling | Reduction over RelationshipGraph (spatial partition) (largely a renaming) |
| Global illumination | PropagationPass + ConvergenceGovernor under `Budget<Microseconds>` |
| Temporal amortization | `Budget<TimeSlot>` + RateLimit + ConvergenceGovernor (feedback) |

Physics Simulation:

| Domain Abstraction | What It Is |
|---|---|
| Broad-phase collision | Reduction over RelationshipGraph (spatial partition); see Section 4.3 for why this is not CompetitiveSelection |
| Narrow-phase collision | CompetitiveSelection (hard): contact pairs compete for resolution priority |
| Constraint solver | PropagationPass + ConvergenceGovernor: iterative relaxation of constraint forces |
| Integration step | ActuationPass: apply force-derived velocity changes to position |

Audio Spatialization:

| Domain Abstraction | What It Is |
|---|---|
| Spatial audio mixer | PropagationPass + `Budget<Voices>`: sound propagates over scene graph under voice budget |
| Audio LOD / culling | QualityHierarchy + TraversalEngine: distant sources at lower fidelity |
| Reverb buses | RelationshipGraph + PropagationPass: signal flows over a routing graph |
| Voice priority | CompetitiveSelection (ranked): voices compete for the K available channels |

Network Replication:

| Domain Abstraction | What It Is |
|---|---|
| Interest management | CompetitiveSelection (ranked): entities compete for relevance to each viewer |
| Bandwidth budget | `FederatedBudget<BytesPerSecond>`: master bandwidth subdivided per viewer |
| Delta compression | `Reduction<(Old, New) -> ChangeRecord>`: aggregate state diffs |
| Reliable channels | RateLimit + ConvergenceGovernor: bound retransmits, converge on acknowledgment |

Container Orchestration:

| Domain Abstraction | What It Is |
|---|---|
| Pod scheduling | CompetitiveSelection (hard): nodes compete for pod placement, fit is the scoring function |
| Resource quotas | `FederatedBudget<CPU/Memory>`: cluster master subdivided per namespace |
| Liveness probes | `Signal<Healthy>` + RateLimit: periodic check at governed rate |
| Reconciliation loop | ConvergenceGovernor + ActuationPass: detect drift, drive toward desired state |

CI/CD Pipelines:

| Domain Abstraction | What It Is |
|---|---|
| Pipeline DAG | `RelationshipGraph<Stage, Dependency>` + TraversalEngine |
| Artifact caching | `ResourceRegistry<BuildInput, BuildOutput>` + `Budget<CacheCapacity>` with content-hash invalidation |
| Parallel test execution | `Budget<Compute>` + `Sampler<TestPartition>`: budget-constrained parallel work |

ETL / Data Pipelines:

| Domain Abstraction | What It Is |
|---|---|
| Extract stage | ActuationPass: I/O-gated data retrieval from a ResourceRegistry (largely a renaming) |
| Mapping stage | ActuationPass: map function over data (largely a renaming) |
| Load stage | ActuationPass + `Budget<DestinationCapacity>` + `ResourceRegistry<Key, Record>` with atomic write boundary |
| Backfill | TraversalEngine over a temporal QualityHierarchy: budget-constrained reprocessing |

Configuration Management:

| Domain Abstraction | What It Is |
|---|---|
| Desired state convergence | ConvergenceGovernor: detect current vs. desired state delta, iterate until converged |
| Idempotent operation | ActuationPass with `Reduction<(Old, New) -> ChangeRecord>`: only actuate if delta is non-zero |
| Role/playbook | `RelationshipGraph<Task, Dependency>` + TraversalEngine: a DAG workload |
| Inventory | `ResourceRegistry<Host, Configuration>` (largely a renaming) |

SOAR (Security Orchestration, Automation, and Response):

| Domain Abstraction | What It Is |
|---|---|
| Playbook | `RelationshipGraph<Action, Dependency>` + TraversalEngine: a DAG workload with capability-gated I/O, aligned with the recorded CI/CD, ETL, and configuration-management recipes |
| Alert triage | CompetitiveSelection (ranked): alerts compete for analyst attention seats, prioritized by severity score |
| Enrichment | ActuationPass + ResourceRegistry: look up context from external sources (largely a renaming) |
| Response action | ActuationPass with capability-based access control |

Distributed Consensus (Raft):

| Domain Abstraction | What It Is |
|---|---|
| Leader election | CompetitiveSelection (hard): nodes compete for the leader seat |
| Log replication | PropagationPass: leader propagates log entries to followers until majority acknowledgment |
| Heartbeat | `Signal<LeaderAlive>` + RateLimit: periodic notification at governed rate |
| Commit | `Reduction<Acknowledgment, Count>` + `Budget<CommitSlot>` + `ResourceRegistry<TxnID, Record>` with atomic commit boundary |

These are component-level structural readings, and the protocol keeps its own semantics: terms, leader authority, quorum intersection, log matching, commit rules, and reconfiguration remain domain content required for Raft's safety and liveness claims.

Economic Simulation:

| Domain Abstraction | What It Is |
|---|---|
| Market order matching | CompetitiveSelection (hard): buy orders compete for sell-order seats, price is the scoring function |
| Price discovery | PropagationPass + ConvergenceGovernor: iterative relaxation toward equilibrium price |
| Inventory management | `Budget<ItemSlots>` + `ResourceRegistry<ItemID, Slot>`: multi-resource updates under capacity constraints with atomic boundary |
| Trade | `Budget<U_source>` + `Budget<U_target>`: atomic exchange between two Budget instances |

Machine Learning (mappings discussed in Section 6):

| Domain Abstraction | What It Is |
|---|---|
| Attention mechanism | CompetitiveSelection (soft): tokens compete for attention weight, similarity is the scoring function, softmax produces weighted combination [2] |
| Backpropagation | PropagationPass (single-pass variant): reverse message passing on the computation graph (precision caveat in Section 6) |
| Speculative decoding | Two-level CompetitiveSelection: fast model generates candidates (coarse), slow model verifies (fine) [8] |
| Beam search | CompetitiveSelection (ranked): candidate continuations compete for K beam seats |
| KV cache | `ResourceRegistry<SequencePosition, (Key, Value)>` + `Budget<CacheCapacity>` with position-based invalidation |
| Learning rate scheduling | `Budget<TimeSlot>` + RateLimit + ConvergenceGovernor (feedback): PID-like control governing a resource (learning rate) over time |
| Early stopping | ConvergenceGovernor: detect when validation loss improvement falls below threshold |
| LoRA / Adapters | `Budget<Parameters>`: constrain trainable parameters to a fraction of total [6] |
| Dropout | `Sampler<ActivationMask>`: probabilistic selection of active neurons |
| Loss computation | `Reduction<Prediction, Scalar>`: aggregate prediction-ground-truth distances |
| Uniform gradient computation | Per-parameter gradient evaluation without relevance gating. The absence of CompetitiveSelection in the gradient path |
| Fixed-interval evaluation | A fixed metric schedule without change-impact selection. The absence of `Signal<ConvergenceChange>` + change-impact analysis |
| Flat parameter training | One training fidelity from step 0. The absence of QualityHierarchy + TraversalEngine in the gradient path |
| Uniform gradient budget | Equal gradient allocation without a learning-need policy. The absence of `FederatedBudget<GradientCompute>` |
| Layer freezing | Binary ConvergenceGovernor (per-group) without graduated states, budget reallocation, or reactivation |
| Curriculum learning | QualityHierarchy over data only, without hierarchy over parameters or budget governance |

---

## 3. Why the Pattern Is Hard to See

### 3.1 Vocabulary as Cognitive Lens

Domain terms preserve distinctions that matter locally. They can also hide a construction shared with another field. A visibility buffer and a scheduler use different nouns, but both may contain scoring, allocation within capacity, exclusive assignment, and a committed effect.

Kleppmann and Alvaro document the same vocabulary split within convergence research: CRDTs, OT, MRDTs, and CALM or invariant confluence arose in separate computer-science communities [a-13]. Their account supports the practical reason for DAC's stripping step: the structural work was neighboring while the vocabularies kept the communities apart.

### 3.2 The Specialization Trap

Specialized communities publish against different problem statements and evaluation criteria. Cross-domain analogies therefore need a structural test. DAC asks whether the state transitions, obligations, and composition requirements match after the local content is removed.

### 3.3 Research Path

DAC grew from an execution-kernel design for ETL, SOAR, and configuration management. The design needed shared resource governance, layered interfaces, composable data flow, and explicit authority. Adjacent orchestration, rendering, routing, and ML systems then widened the survey.

Individual comparisons in this paper have precedents within their source domains. The research contribution is the repeatable decomposition and reconstruction method, the catalog it produced, and the formal questions attached to each candidate.

---

## 4. The Competitive Selection Family

### 4.1 The Overcounting Problem

The original SlotArbitrationPass mapping covered over seventeen domain patterns, including visibility buffers, attention, scheduling, market matching, beam search, election, and collision detection. That breadth prompted a review of whether the entries shared an allocation contract or merely competitive terminology.

The revised account treats this as a family. Candidates are scored against seats, then a mode governs allocation, and the allocation obligation distinguishes the modes.

### 4.2 Three Selection Modes

The modes share the scoring interface and AllocationRecord, while their allocation obligations differ.

| Mode | Characteristic allocation obligation | Example realizations |
|---|---|---|
| Hard | one winner per seat under a declared tie rule | argmax, exclusive scheduler |
| Soft | positive shares within the allocation limit; a fixed terminal total; higher scores do not receive lower shares | softmax-shaped domain mappings, divisor apportionment |
| Ranked | multiple winners under a declared count or resource cap | top-k, priority queue |

The realization is domain-supplied. Differentiability, score transformation, and algorithmic cost belong to that realization rather than the family name.

### 4.3 Reclassified Mappings

Two patterns originally mapped to this family deserved separate scrutiny, and both were reclassified.

Anomaly detection, described in some formulations as "not winning the normal slot," is better characterized as a Reduction (compute a distance metric from a reference distribution) followed by a threshold comparison. Forcing it into the competitive selection frame added vocabulary without adding structural insight.

Broad-phase collision detection is primarily spatial partitioning and filtering. A processing budget may add competition, but competition is not intrinsic to the overlap test. Section 2.5 therefore maps it to Reduction plus spatial partitioning.

This paper records the mapping dispositions and residuals; [reference.md](reference.md) records the resulting catalog classifications.

---

## 5. The LeanFormer Feasibility Experiment

LeanFormer tested whether the sixteen hypothesized entries could turn a system description into an implementation plan. Machine learning was chosen because it was outside the author's research background. None of the entries had yet been formally tested.

The design treated catastrophic forgetting as destructive shared-state writes and the training loop as resource-governed orchestration. It used an immutable base, registry-managed overlays, budgets, staged activation, convergence control, and audit. The artifact ran at 39M and 204M parameters, with the recorded local checks holding at their stated limits. Later literature comparison found overlap with LoRA-style deltas [6], sparse attention, and hierarchical training.

The research proceeded on that initial success, and the experiment has not been modified since. The full report, including the six stripped problems, the construction procedure, the B=0 diagnostic episode, the measurement table, and what remains unmeasured, is [leanformer.md](leanformer.md). The current-catalog reconstruction, located by [research.md](research.md), audits the frozen design against the evolved catalog and records changed classifications and residuals.

---

## 6. The ML Mappings

The ML mappings test the catalog against a later domain in the survey. They are structural readings of recorded mechanisms rather than claims about their full mathematical or implementation detail.

Transformer attention admits a soft-selection description: query-key similarity supplies scores, softmax supplies normalized weights, and the value vectors contribute under those weights [2]. The mapping preserves the allocation shape while leaving the attention mathematics as domain content.

Backpropagation admits a graph-propagation description: a reverse pass carries gradients through a computation DAG under the chain rule. The accepted mapping is limited to reverse dependency order and message movement. Fixed-point iteration is absent, so this is a partial structural recurrence rather than a claim that the canonical fixed-point PropagationPass implements backpropagation.

Speculative decoding maps to a coarse candidate pass followed by verification and accepted-token actuation [8]. The same recipe appears in surveyed fidelity pipelines, subject to different domain functions and correctness conditions.

---

## 7. The DAG Workload Pattern

### 7.1 Four Domains, One Pattern

The survey found a shared recipe across CI/CD pipelines, ETL workflows, configuration management playbooks, and SOAR playbooks. The recorded examples use directed task graphs with typed dependencies, resource constraints, and controlled I/O at task boundaries. Their trigger rules, task functions, persistence, and product obligations remain domain-specific.

A builder can therefore consider a shared execution core for the common graph progression and resource structures, with product-specific triggers, connectors, policy, storage, and task semantics as explicit layers around that core. Workflow-pattern research provides related control-flow vocabulary [a-9].

### 7.2 Why This Pattern Was Hard to Notice

CI/CD, ETL, configuration management, and SOAR use different product vocabularies for related task-graph behavior. DAC compares the graph progression while retaining task functions and product obligations as domain content.

The companion *Execution Structures* paper treats execution as a separate choice: sequential, fork-join, step graph, stream graph, or a composition. A primitive can participate in any of them; the workload and its progress requirements determine the selection.

---

## 8. Composition Patterns

### 8.1 How Domains Are Reconstructed

The following table gives representative reconstruction recipes from the surveyed systems. This paper records the mapping set and residuals; [reference.md](reference.md) supplies builder-facing recipes and current classifications.

| Pattern | Core Primitives | Governance |
|---------|----------------|------------|
| LOD / Quality scaling | QualityHierarchy + TraversalEngine + CompetitiveSelection + AllocationSnapshot | `Budget<Bytes>` |
| Global illumination | PropagationPass + ConvergenceGovernor | `Budget<Microseconds>` + `Budget<TimeSlot>` + RateLimit + ConvergenceGovernor (feedback) |
| Physics simulation | Reduction + CompetitiveSelection (hard) + PropagationPass + ActuationPass | `Budget<Microseconds>` + ConvergenceGovernor |
| Network sync | PropagationPass + TraversalEngine + `Reduction<(Old, New) -> ChangeRecord>` | `FederatedBudget<BytesPerSecond>` |
| Container orchestration | QualityHierarchy + TraversalEngine + ActuationPass | `Budget<CPU/Memory>` + ConvergenceGovernor |
| CI/CD pipeline | RelationshipGraph + TraversalEngine + ActuationPass | `Budget<Compute>` |
| ETL pipeline | RelationshipGraph + ActuationPass + `Budget<DestinationCapacity>` + `ResourceRegistry<Key, Record>` with atomic write boundary | `Budget<Microseconds>` |
| Configuration management | `Reduction<(Old, New) -> ChangeRecord>` + ConvergenceGovernor + ActuationPass | (none) |
| SOAR playbook | RelationshipGraph + TraversalEngine + ActuationPass | Capability-gated I/O |
| Market simulation | CompetitiveSelection (hard) + PropagationPass + `Budget<U_source>` + `Budget<U_target>` + `ResourceRegistry<OrderID, Order>` with atomic transaction boundary | FederatedBudget + ConvergenceGovernor |
| ML training loop | ActuationPass + Reduction + PropagationPass | ConvergenceGovernor + `Budget<TimeSlot>` + RateLimit (feedback) |
| ML inference | ActuationPass + CompetitiveSelection (soft) + `ResourceRegistry<Key, Value>` + `Budget<CacheCapacity>` | `Budget<FLOPs>` |
| Belief delta system | `Budget<Parameters>` + ResourceRegistry + CompetitiveSelection (ranked) with atomic write boundary | AuditSink |
| Targeted training pipeline | CompetitiveSelection (ranked) + `FederatedBudget<GradientCompute>` + QualityHierarchy + ActuationPass + Signal | ConvergenceGovernorPhaseAware (per-group) + AuditSink |
| Governed data pipeline | `QualityHierarchy<SampleDifficulty>` + CompetitiveSelection (ranked) + Sampler | `Budget<SamplesPerStep>` + AuditSink |
| Change-triggered evaluation | `Signal<ConvergenceChange>` + CompetitiveSelection (ranked) + ActuationPass + Reduction | `Budget<EvalCompute>` + ConvergenceGovernor (per-metric) + AuditSink |
| Readiness-gated knowledge forge | `Signal<GroupConverged>` + ConvergenceGovernor + CompetitiveSelection (ranked) + ActuationPass + Reduction | `Budget<ForgeCompute>` + AuditSink |

In these recipes, catalog entries provide the governed construction while the domain supplies the computation. Recipes that rely on atomicity record it as a runtime given (Section 2.2).

### 8.2 Structure vs. Function

Domain functions include rendering equations, physical laws, Raft's replication rule, ML loss functions, and attention scoring. A catalog recipe must leave those semantics with the domain.

The soft selection form states abstract allocation obligations such as positive shares within the allocation limit and score-relative monotonicity. The transformation that realizes those shares is domain supplied. Softmax is the transformation in the attention mapping; it is not produced by the catalog merely because the mapping uses CompetitiveSelection in soft mode.

The catalog supplies reusable construction and governance contracts; the domain supplies the computation they govern.

---

## 9. Evidence and Revision

### 9.1 Tests Applied to a Mapping

A cross-domain mapping becomes useful to the research through four recorded tests:

1. Survey coverage: each claimed surveyed system has a recipe or an explicit residual.
2. Behavioral fidelity: a representative realization preserves the source behavior under stated inputs and assumptions.
3. Obligation fidelity: the recipe preserves the source responsibility, identifies its decisive behavior, and survives a discriminating control at the recorded evidence level.
4. Construction value: the mapping produces a reusable implementation, proof pattern, diagnosis, or transfer result for a builder.

These tests have separate outcomes. The algorithmic corpus supplies behavioral comparisons against independent references. LeanFormer supplies construction evidence under its own recorded specifications. The formal artifacts test obligation and refinement claims. Survey coverage remains scoped by the inventory used to make the mapping.

Minimality is a separate, relative question. A current primitive resists the tested reductions over the pinned connective vocabulary while preserving both behavior and obligation placement. A successful reduction reclassifies the entry as a named composition. [reference.md](reference.md) records those decisions, because the answer can change when the connective vocabulary or test improves.

Independent recurrence supplies another kind of evidence. Standard libraries contain folds, semaphores, maps, channels, token buckets, distributions, and hierarchical quotas that resemble entries or named compositions in this catalog. Kleppmann and Alvaro's convergence survey and the Livelymerge note provide two more examples of neighboring structures reached through different domain questions [a-13, a-16]. Recurrence makes a candidate worth testing; each entry then stands on its own recorded obligation evidence.

### 9.2 What the Twelve Domains Cover

The initial domains are concentrated in resource-governed execution systems where work often moves through a graph under capacity constraints. The catalog's performance in that family is evidence about that family. Systems with different computational character require separate survey and residual tests; Section 9.2.1 reports a test against one such family, and interactive theorem proving, term rewriting, and pure symbolic computation remain untested. The executable examples extend the survey past the original twelve domains: real-time scheduling, transactional memory, replicated data, and differential-privacy accounting each received a registered reconstruction from catalog parts ([Formal Examples](../formal/examples/README.md)).

### 9.2.1 The Algorithmic-Corpus Stress Test

The catalog was stress-tested against a classical-algorithm corpus outside the initial resource-governed systems. That supplementary corpus is derivation provenance rather than a primary theory claim.

Most of the corpus received recipes over the initial vocabulary. Memoization, for example, mapped to ResourceRegistry + TraversalEngine + Reduction; monotonic stack and deque structures mapped to ResourceRegistry + ActuationPass + Reduction. The memoization mapping is now executable: one shared composition runs ten dynamic-programming algorithms against separately written references ([Formal Examples](../formal/examples/README.md)). The unresolved patterns led to three additions in that campaign:

Bisection, monotonic interval halving, with Halving, MonotonicityPreservation, ProbeBound, and EventualConvergence as contract clauses. Used by 6 algorithms in the corpus.

EquivalenceClass, union-find partition maintenance, with RepresentativeIdempotence, RankMonotonicity, and RepresentativeRootedness as the structural checks. (Symmetry and Transitivity, listed as invariants in earlier versions, hold as properties of equality itself for any representative function; negative-control checking confirmed no mutation can falsify them, and they are retained as annotated definitions rather than checked invariants.) Used by 2 algorithms.

BacktrackingTraversal, depth-first search with paired do/undo state restoration, with Pairing, StateRestoration, and RecordedLeafValidity as invariants. RecordedLeafValidity checks only recorded visits; it does not establish full leaf coverage. Used by 5 backtracking algorithms in the corpus.

The historical campaign added a TLA+ specification and decomposition check for each new candidate, with counterexamples targeting Halving, RepresentativeRootedness, and Pairing. Later minimality work changed catalog classifications, so [reference.md](reference.md) records current membership.

The first algorithm corpus required three additions to the initial catalog. Retaining the mismatches led to those revisions.

### 9.3 What Each Kind of Evidence Establishes

The original campaign used TLC to enumerate reachable states in finite configurations. A pass supports the property in that configuration; a counterexample supplies a failure trace. A theorem over other configurations requires proof beyond the TLC run.

TLAPS proofs, model checks, implementation contracts, known-answer tests, and training measurements answer different questions, so the research records each result with its assumptions, bounds, controls, and refinement gap. An observed invariant during a LeanFormer run is execution evidence for that artifact, not a proof over other sizes or implementations.

The active artifact set contains verified Rust implementations and action-level correspondence for every current catalog structure. The nineteen primitive and named-composition contracts also have mechanized refinement packages between their written executable transition profiles and canonical models. Those packages establish their named mappings. They do not decide which clauses are primary obligations, supporting facts, or derived results. Verus verifies the written executable contracts, and the semantic ledgers own correspondence to TLA+. The exact formal selectors and current obligation-model gap are recorded in [formal-methods.md](formal-methods.md).

### 9.4 Formal Verification: Results

The paper's original campaign formalized the reported primitive, decomposition, and LeanFormer composition specifications in TLA+ [14] and checked finite configurations with TLC. Those names and counts describe the historical campaign; current catalog-wide claims rest on the active artifact set, its controls, and the full validation contract.

The reported primitive configurations passed their listed safety checks at the tested bounds, and the LeanFormer composition configurations passed theirs. The decomposition configurations produced check-act counterexamples at their tested bounds, including the phase-unaware ConvergenceGovernor trace corresponding to the B=0 initialization failure reported in [leanformer.md](leanformer.md). These results motivated the obligation-boundary test: they are finite witnesses that the tested decompositions opened an interference interval in which the listed invariant could fail.

The verification process challenged and corrected five initial assumptions about the formal specifications.

| Specification | Initial Assumption | TLC Finding | Correction |
|---|---|---|---|
| ConvergenceGatedActivation | Proposed global invariant | L0 can regress to ACTIVE after L1 activates (AWAKENED mechanism) | Reclassified as precondition of ActivateNextLevel |
| FullDepthMeansUncertain | Full depth implies no convergence | Convergence at the final layer is valid | Corrected to: full depth with no convergence at any layer implies uncertainty |
| ForgingRequiresConvergence | Proposed phase-independent invariant | Converged group could revert to ACTIVE during forging | Restricted governor updates to training phase |
| Budget reallocation | Free half of converged group's budget | Group may have consumed more than half; this can violate SubPoolCapacityBound | Free only the unused portion |
| WinnerOptimality | Holds between evaluations | Score update between evaluations creates stale winner | Invalidate allocation when scores change (TOCTOU pattern) |

The five findings changed the corresponding specifications. They also show why the formal work is allowed to revise the paper's candidate definitions.

### 9.4.1 Minimality Refinement Results

The historical decomposition results are intra-entry checks. Minimality asks a separate question: can one candidate be rebuilt from other entries plus admitted connective forms while preserving its behavior and obligation placement? The original campaign checked RateLimit and Signal in the constructive direction.

The method follows the TLC refinement idiom in Lamport's *Specifying Systems*, Section 5.8. Each candidate construction contains the proposed building blocks plus admitted glue. A refinement map relates construction state to target state, and the finite check tests whether the construction's behaviors satisfy the instantiated target specification. A passing check supports the reduction at that configuration; the paired control tests whether the correspondence check can distinguish a known break.

Glue admissibility follows a stated rule: glue carries no governance obligation. The clock, window marker, and read cursors in these constructions are runtime or connective state, and the checked obligations belong to building-block entries or the target. Without a pinned rule, minimality would depend on how much behavior the glue is allowed to contain.

Both candidates are reducible in the retained finite configurations:

| Candidate | Built from | Glue | Retained result |
|---|---|---|---|
| RateLimit | `Budget<Operations>` | clock, window start | Refinement holds at the generated report's configured bounds |
| `Signal<T>` | AuditSink | per-listener pull cursor | Refinement holds at the generated report's configured bounds |

For RateLimit, the windowed counter maps to a Budget allocation, its cap maps to capacity, and a window rollover releases the balance before the next allocation in one modeled transition. The reduction depends on the recorded convention that the clock is a runtime given. For Signal, a value change maps to an AuditSink append and each listener holds a read cursor; the head and cursor positions derive pending and acknowledged state, and the hash chain adds storage cost to the construction.

A refinement property can pass under a faulty mapping, so the campaign paired each construction with a negative control that changed one correspondence-relevant step while retaining the local invariant checks.

| Negative control | The break | Local invariants | TLC verdict |
|---|---|---|---|
| RateLimit construction | window rollover omits `window_start' = clock` | still pass | Violates RateLimit's action property at the retained bound |
| Signal construction | value change drops the `v /= current_value` filter | still pass | Violates Signal's action property at the retained bound |

The two controls failed on the target action property while their local invariant checks passed, which discriminated the known breaks at the recorded bounds.

The original results supported reclassifying Signal and RateLimit as named compositions. The retained classification applies a stronger two-part criterion: behavioral refinement and obligation placement must be reproduced together over the pinned connective vocabulary. Current classification comes from [reference.md](reference.md); [research.md](research.md) locates the supporting minimality study.

### 9.5 Evidence Disposition

The results above apply to the particular properties named by their proofs and checks. The
construction registry groups the contract clauses by the responsibilities they express: it
classifies 69 clause occurrences into 36 obligation schemas. The
[ALK claim package](alk-claims.md) connects Budget and Sequential to their actual predicates and
actions at declared claim frames. Other catalog selections and ALK profiles still need their own
refinement arguments.

The finite mapping ledger records the unresolved parts of each reconstruction. LeanFormer's
frozen design has also been reconstructed against the current catalog. That record identifies
which classifications changed, what the domain and runtime supply, and what remains unexplained.

---

## References

[1] Brooks, F.P. (1987). No Silver Bullet: Essence and Accident in Software Engineering. IEEE Computer, 20(4), 10-19.

[2] Vaswani, A. et al. (2017). Attention Is All You Need. Advances in Neural Information Processing Systems, 30.

[6] Hu, E.J. et al. (2021). LoRA: Low-Rank Adaptation of Large Language Models. arXiv:2106.09685.

[8] Leviathan, Y. et al. (2023). Fast Inference from Transformers via Speculative Decoding. ICML 2023.

[14] Lamport, L. (2002). Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers. Addison-Wesley.

[a-1] Alexander, C. et al. (1977). A Pattern Language: Towns, Buildings, Construction. Oxford University Press.

[a-2] Gamma, E., Helm, R., Johnson, R., and Vlissides, J. (1994). Design Patterns: Elements of Reusable Object-Oriented Software. Addison-Wesley.

[a-3] Parnas, D.L. (1972). On the Criteria To Be Used in Decomposing Systems into Modules. Communications of the ACM, 15(12), 1053-1058.

[a-4] Liskov, B. and Zilles, S. (1974). Programming with Abstract Data Types. SIGPLAN Notices, 9(4), 50-59.

[a-5] Gelernter, D. (1985). Generative Communication in Linda. ACM Transactions on Programming Languages and Systems, 7(1), 80-112.

[a-6] Hoare, C.A.R. (1978). Communicating Sequential Processes. Communications of the ACM, 21(8), 666-677.

[a-7] Hewitt, C., Bishop, P., and Steiger, R. (1973). A Universal Modular ACTOR Formalism for Artificial Intelligence. IJCAI 1973.

[a-8] Wing, J.M. (2006). Computational Thinking. Communications of the ACM, 49(3), 33-35.

[a-9] van der Aalst, W.M.P. et al. (2003). Workflow Patterns. Distributed and Parallel Databases, 14(1), 5-51.

[a-10] Cole, M. (1989). Algorithmic Skeletons: Structured Management of Parallel Computation. Pitman / MIT Press.

[a-11] Mattson, T., Sanders, B., and Massingill, B. (2004). Patterns for Parallel Programming. Addison-Wesley.

[a-12] McCool, M., Robison, A.D., and Reinders, J. (2012). Structured Parallel Programming: Patterns for Efficient Computation. Morgan Kaufmann.

[a-13] Kleppmann, M. and Alvaro, P. (2022). Research for Practice: Convergence. ACM Queue, 20(3), 88-95. https://queue.acm.org/detail.cfm?id=3546931

[a-16] Warth, A., Ingalls, D., and van Hardenberg, P. (2026). Convergence Is Not Enough. Ink & Switch, Livelymerge Notes, July 2026. https://www.inkandswitch.com/livelymerge/notebook/lm-02/
