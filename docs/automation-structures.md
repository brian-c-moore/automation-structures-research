# Automation Structures

## A Structural Theory for Automated Systems

---

## Abstract

Automation Structures Research provides a catalog of reusable state-machine abstractions, organized around behavioral obligations, with explicit contracts and conditions for composition. The theory explains why these abstractions were selected and how to build with them. A budget must keep admitted use within capacity; an audit path must preserve the required evidence. Each structure defines a reusable obligation schema. A design applies it to a concrete subject and scope, states the failures it must withstand, and identifies who controls its fulfillment. The construction method checks how those responsibilities hold when the parts are assembled.

The `automation-structures` Rust library implements the reusable state machines. `alk-core` is being built by composing them into an automation kernel, with components and flows as the developer's construction model. The specifications describe state and behavior; the engineering construction establishes responsibility and enforcement authority for their use.

The catalog has 23 entries with TLA+ specifications, TLAPS proofs, and Verus implementations for their written contracts. Composition theorems prove preservation under stated conditions. A Budget/Sequential example follows two contracts through modeled actions and owner-issued claim records. Section 10 records the evidence and what would refute each claim.

---

## 1. Introduction

### 1.1 The question

The decision to automate a task makes the system responsible for the behavior people rely on, whether anyone writes it down or not. A script that rotates logs is trusted not to delete the wrong files. A deployment pipeline is trusted not to skip its checks. This research asks which of those responsibilities have reusable forms that can be implemented and verified across domains.

A survey of twelve engineering domains found recurring forms: allocation under a budget, capacity-limited pools, convergence-governed iteration, and tamper-evident mutation records. Removing domain vocabulary made these forms easier to compare. Section 8.4 demonstrates one recurrence by running rendering level-of-detail selection and route selection through the same executable composition.

### 1.2 The machine-elements analogy

A machine-elements catalog names reusable parts such as bearings, gears, and springs, with their limits and failure modes. Automation Structures uses the same approach for software: identify recurring constructions, state their contracts, and give builders tested ways to combine them. The chosen abstraction is useful when it makes those choices easier to implement and verify.

The catalog covers the systems examined and changes when a reduction or unexplained behavior challenges an entry. Prior work provides comparisons: [Kleppmann and Alvaro's convergence survey](https://queue.acm.org/detail.cfm?id=3546931) describes four approaches developed in separate computer-science communities. Domain Abstraction Collapse (DAC) uses a shared vocabulary to compare such work while retaining each source's semantics.

### 1.3 Two ways in

For construction, read Sections 2 and 3, then use the procedure in Section 8.1 with Sections 4-6 as reference. For review, start with the claims and evidence in Section 10. Appendix A identifies the companion paper and formal artifacts for each result.

---

## 2. The Layer

### 2.1 Two boundaries

The lower boundary is where a system accepts responsibility for behavior that can fail. A pool of items is ordinary state. When a design promises that admitted use will stay within capacity, it instantiates a Budget obligation. Another caller can violate that safety obligation between check and commit. Progress can instead fail through inaction or unfair scheduling, and evidence can fail through omission, corruption, or lost custody. The general test is the accepted responsibility; a falsifying interleaving is one safety-specific way to expose it. Section 3.4 turns the test into a procedure.

The boundary concerns accepted responsibilities, regardless of programming language. Arithmetic and plain data types sit below it; semaphores and quota types can implement responsibilities above it. Their presence in standard libraries provides examples of the same recurring forms.

In [Convergence Is Not Enough](https://www.inkandswitch.com/livelymerge/notebook/lm-02/), Warth, Ingalls, and van Hardenberg report replicas that converge while merged linked lists become truncated or cyclic. Replica convergence holds, but the merge does not preserve the application invariant. They propose defining merge behavior through abstract-type operations. DAC and the Execution Integrity Model (EIM) interpret this as a check-act problem: a check against an earlier state cannot license a later write unless the required condition remains true at commit.

The convergence survey identifies a related coordination requirement for limited resources: an account must not be overdrawn, and a seat must not be sold twice. CALM and invariant confluence formalize when coordination can be avoided. In this catalog, the account maps to Budget and exclusive seat allocation to CompetitiveSelection's hard mode. These are structural comparisons; the replicated JSON case study in Section 8.4 separately tests a reconstruction against the convergence literature.

The upper boundary separates the structure from its domain content. Rendering triangles, cluster pods, and network routes differ, while allocation, selection, traversal, and mutation recording can share a construction. In `Budget<U>`, Budget defines the capacity invariant and `U` identifies the resource. The invariant does not inspect `U`, so the same specification can govern VRAM, probes, operations, or samples.

A reusable construction between those boundaries, independent of the content that fills it, is an automation structure. The research studies its parts, execution structures, workload shapes, and enforcement placement as separate questions.

### 2.2 The strata of a composition

A composition records four strata:

| Stratum | Supplied by | Carries | Examples |
|---|---|---|---|
| Runtime givens | the environment | assumptions, not state | atomicity, time |
| Abstraction primitives | the catalog (Section 3) | a reusable obligation schema | Budget, AuditSink, ConvergenceGovernor |
| Connective forms | the composition (Section 3.5) | state or logic role, no independent obligation schema | Projection, Cursor, Accumulator, Marker, Counter, Buffer, OrderingPass |
| Domain parameters | the domain | content filling form slots | scoring functions, operators, value types |

For example, a VRAM budget uses the Budget contract with a memory resource type.
A guard is the owning structure's admission predicate and stays coupled to that
owner's update or refusal. A window names a particular construction: RateLimit
uses a window-start Marker and runtime clock with Budget accounting, while
ConvergenceGovernor retains a chronological Buffer view and its checked history
couples that Buffer to the exact-sum Budget. A join belongs to ForkJoin or an
explicitly named composition with a selected closure contract. These terms do
not extend the seven-form vocabulary. Section 2.2 of
[Execution Structures](execution-structures.md) maps their admitted actions and
retained state. Runtime givens such as atomicity and time are environmental
assumptions. A construction must state which of those assumptions its contracts
require.

### 2.3 A working definition of automation

Automation, in this paper, begins when a built system executes work under a stated obligation without a human enforcing each step. The design must then identify the obligation-decisive behavior and its enforcement owner, or record the trust boundary, assurance profile, and failure left when that authority is external. A human approval can stay in the loop; EIM records the exact obligation the person owns and the assurance path for every party outside that authority.

---

## 3. Statics: The Parts

*Companion: Domain Abstraction Collapse. [reference.md](reference.md) holds current membership and classifications.*

### 3.1 What an abstraction primitive is

An abstraction primitive is a reusable unit whose obligation-bearing behavior is not supplied by a validated composition of other entries over the pinned connective vocabulary. This is the current classification at the chosen abstraction, open to revision by a faithful reduction. A primitive may need several clauses, offer alternative modes, or carry multiple distinct obligations. A successful reduction reclassifies it as a named composition, preserving its name and recording its recipe.

### 3.2 The catalog

The catalog currently holds 23 entries: nine abstraction primitives, ten named compositions built from them, and the four execution structures of Section 4 on a separate selection axis. Each structure contract may define an obligation schema; a construction selects and instantiates only the contracts and modes it uses. The catalog was built by collapsing surveyed systems to structural descriptions, then stress-testing the result against classic algorithms from outside those domains. Behavior a mapping could not account for was recorded as a residual. [reference.md](reference.md) lists all 23 entries with their roles; the tables below show all nine primitives by family.

Data primitives, for how data is structured and related:

| Primitive | Current obligation-bearing role |
|---|---|
| `Budget<U>` | A three-ledger pool with the invariant `allocated + reserved + pending_eviction <= capacity` |
| QualityHierarchy | A tree of representations at multiple fidelity levels |
| `ResourceRegistry<K,V>` | A unique key-to-value mapping |

Control primitives, for how computation is organized:

| Primitive | Current obligation-bearing role |
|---|---|
| CompetitiveSelection | Allocate candidates to seats under a scoring function, in three modes: hard (one winner per seat), soft (positive discrete shares within the allocation limit under a fixed terminal total), ranked (top items until the budget is spent) |
| ActuationPass | Apply a side-effecting operation to a set of items |
| PropagationPass | Snapshot-isolated graph updates with a declared round limit; domain convergence stays external |

Coordination primitives, for how the system observes and governs itself:

| Primitive | Current obligation-bearing role |
|---|---|
| ConvergenceGovernor | Detect fixed-point convergence and govern iteration, via a phase machine with a no-skip property |
| AuditSink | A hash-chained append-only log of mutations |

Algorithmic primitives, added by the out-of-family stress test:

| Primitive | Current obligation-bearing role |
|---|---|
| BacktrackingTraversal | Depth-first search with paired do/undo state restoration and valid recorded full-depth visits |

The ten named compositions are operations that recur by name but are buildable from other entries. Mechanical minimality checking proved that `Signal<T>`, a typed event channel, is an AuditSink plus a predicate-filtered pull consumer, and that RateLimit, a per-window operation bound, is `Budget<Operations>` plus a clock-driven window reset, with the clock a runtime given. Both keep their names and recipes. A named composition occupies the same recipe positions a primitive does, with its internal reduction explicit; reference.md records what each of the ten reduces to.

SelectThenActuate and TraversalBudgetComposition are different in kind: they are verified statements about the catalog rather than entries in it, each proving that its constituent primitives' invariants survive one specific composition. A named composition is a unit to build with. A composition theorem is evidence about how units combine.

### 3.3 One worked recurrence

One recurrence shows the pattern: for a consumer or seat, score the eligible candidates under a supplied policy, then choose or combine them before committing the downstream effect. Rendering quality selection and per-viewer network replication both use the ranked form and compose it with a capacity Budget. Transformer attention has a narrower soft reading: query-key scoring supplies the candidates, and the softmax mathematics that normalizes their weights stays on the domain side of the boundary. These mechanisms share CompetitiveSelection's structure while keeping their own semantics. Section 8.4 provides a separate executable example: rendering level-of-detail selection and route selection reuse CompetitiveSelection within the same `rooted_frontier` composition. The full mappings are in the DAC paper and [formal-methods.md](formal-methods.md).

### 3.4 Evidence and the obligation test

The evidence behind the catalog combines finite-state model checking in TLC, machine-checked TLAPS proofs of the stated safety and liveness properties, Verus implementations proved against their written contracts, and negative controls confirming that each check can catch the violation it exists to catch. [formal-methods.md](formal-methods.md) locates every unit and gives the command that runs it. All 23 entries also carry a mechanized refinement package connecting specification to implementation through named state and action mappings; each package establishes those mappings and nothing broader.

The boundary test from Section 2.1 becomes a procedure here. Name the responsibility, its subject, and how it can fail: an unsafe action, missing progress, a bad trace relation, or missing evidence. Then identify the behavior that decides the outcome and ask whether the candidate defines a reusable rule for governing it. A role that only carries state or position under another contract is connective. For safety claims, separating check from commit should expose a discriminating interleaving. Recurrence alone never admits an entry.

A formal contract may use several clauses to state one obligation. Type facts, assumptions, helper invariants, and derived corollaries support that contract without becoming additional obligations. Alternative modes supply alternative contracts; selecting one mode does not import every other mode's clauses.

The construction registry makes that distinction explicit: it relates 36 obligation schemas to
69 clause occurrences across the 23 catalog entries. It records which clauses state each
responsibility, which support its proof, and which belong to alternative modes. The
[ALK Claims guide](alk-claims.md) follows two of those schemas into a modeled system.

### 3.5 The stratum beneath: connective forms

The recipes use seven connective forms: Projection, Cursor, Accumulator, Marker, Counter, Buffer, and OrderingPass. These roles carry state or logic without defining an independent obligation schema. G v1.1 fixes the vocabulary in [reference.md](reference.md), so each reduction has a stable basis: specified entries composed using specified connective forms.

Entries cross the boundary in both directions. A connective form becomes a primitive candidate when it must define an independent obligation schema. A primitive becomes a named composition when a tested reduction supplies that schema from other entries; Signal and RateLimit both made that move.

### 3.6 The catalog's history is part of the evidence

Formal results have changed catalog membership. The algorithm corpus introduced search with retraction and monotone halving. Refinement checks reclassified Signal and RateLimit as named compositions. Another demotion was reversed when a faithful model exposed behavior that the earlier specification had frozen. The retained history records the evidence for each decision.

---

## 4. Dynamics: Execution Structures

*Companion: Execution Structures. Its derivation, builder method, and evidence live there.*

### 4.1 The builder's question

An execution structure determines how admitted work starts, advances, hands off results, and closes. Its execution profile records concurrent activity, dependencies, progress grain, handoff, and persistence. The catalog offers four structures; profile comparisons test their distinctions.

### 4.2 The four structures

| Structure | How work proceeds |
|---|---|
| Sequential | One logical work locus at a time, with visible transitions in a declared order |
| Fork-join | Sibling units fan out in parallel and resolve under an explicit join rule |
| Step graph | Operators become eligible when predecessors complete, run to completion, and publish results downstream |
| Stream graph | Operators process records while upstream operators stay active, under a flow-control rule |

Step graph is the natural shape of build pipelines and workflow engines; stream graph is the natural shape of continuous dataflow. What separates them is the unit of completion: a step graph finishes stages, while a stream graph makes per-record progress. Production stream processors expose both as exchange modes over the same operator graph, which is the operational precedent for keeping them distinct. The formal artifacts for all four live under `formal/execution/carriers/`; those paths use "carrier" as a synonym for execution structure.

### 4.3 The refinement hierarchy

Under the written mappings, Sequential and ForkJoin refine StepGraph, and StepGraph refines StreamGraph: every behavior of the smaller structure can be represented in the larger one, within the stated observation model. Distinctness witnesses show the separation in the other direction, exhibiting behaviors of the larger structure that the smaller can't represent. Together they order the four by expressive power without ranking them by cost.

The builder guidance follows. Start with the smallest structure that faithfully represents the workload's progress and failure contract, and compose structures where boundaries differ. A mature runtime already in place, operational constraints, or an obligation carried at a seam can justify a more general choice.

Actors sit on a different axis. The actor model describes what gets executed and how it is addressed: identity, private mailboxes, behavior replacement, dynamic topology, supervision. An actor's handler may run sequentially, fork-join internally, drive a step graph, or drive a stream graph, and the surveyed actor systems map to each of the four at different boundaries. A handler receives an execution-structure classification once its boundary and progress grain are chosen.

---

## 5. Work: The Shape of the Computation

Execution structures describe how a runtime moves. Workloads have dependency structures of their own, and the two are independent axes. Ordering is the heuristic for the shape of the workload: the dependency structure of the computation itself, as distinct from the shape of the input data. The distinction matters because a cyclic input graph is often walked by an acyclic computation.

| Ordering class | Shape of the computation's dependencies |
|---|---|
| Linear | a single chain of dependent steps |
| Tree | branching without reconvergence |
| DAG with reconvergence | acyclic dependencies whose reconvergence requires more than a tree |
| Graph-with-cycles | dependencies that feed back; fixed points and iteration |

Ordering informs the selection without deciding it. Linear work maps cleanly to Sequential, branching sibling work suggests Fork-join, reconvergent dependencies suggest a step graph, and cycles demand an explicit iteration or convergence rule in whatever structure is chosen. The boundary, the visible progress grain, the failure contract, and the operational constraints complete the decision.

For work whose dependencies form a graph, one field test does most of the sorting. When a value finishes flowing through, does node-local state reset, or does it carry over while records keep arriving? Reset means the graph is a single computation that runs to completion: a step graph. Carry-over means a dataflow that stays active: a stream graph. Crossed with invocation (pull, where the consumer demands and computation recurses backward; push, where sources fire and values propagate forward), the test yields the four quadrants used to classify the surveyed graph runtimes. Below the quadrants sits ordinary configuration: memoization, snapshotting, flow control, failure semantics, and the other choices the Execution Structures paper walks through.

---

## 6. Placement: Ownership and Assurance

*Companions: [Claim-Relative Ownership and Assurance](claim-relative-ownership.md) defines the
cross-abstraction ownership model. The Execution Integrity Model applies it to execution placement,
assurance, and failure.*

### 6.1 Where execution changes hands

The EIM vocabulary was derived from the catalog: identify each primary obligation schema, instantiate it for the system, and locate all behavior that can decide it. Related concerns are grouped for navigation without merging distinct obligations. Four surfaces organize where application execution changes; two planes cut across all four.

| EIM term | Structural content |
|---|---|
| Scheduling surface | Eligibility, capacity, dependency release, progress, retry, and termination |
| Isolation surface | Authoritative state association, partitioned capacity, effect scope, and mediated access |
| Execution surface | Module identity and provenance, resource use within declared limits, restoration, effect fidelity, and truthful closure |
| Transport surface | Endpoint relations, queue bounds, rate limits, signals, ordering, delivery, and flow control |
| Governance plane | Instantiated obligations over the selected execution surfaces |
| Observation plane | Evidence about governed commits and trace outcomes; custody and assurance of that evidence |

The Parkerian Hexad was used as an outside check that the classical security attributes are covered; the derivation itself comes only from the catalog schemas and their concern groupings.

### 6.2 The record an EIM review produces

An EIM review starts from a declared application claim and failure model, instantiates the obligations the application uses, locates the transitions that can fulfill or violate them, and produces an ownership and assurance map. The map answers seven questions.

| Record field | Question answered |
|---|---|
| Claim frame | Which subject, obligation, mode, scope, observation boundary, authority boundary, claimant, failure model, abstraction, lifecycle phase, and property form define the claim? |
| Governed transition | Which enabling condition, state change, commit point, and trace outcome can fulfill or violate it? |
| Canonical enforcement owner and delegate | Which one authority or named protocol covers the obligation-decisive behavior at this frame, which work is delegated, and which authority lies outside the boundary? |
| Assurance | Which claimant, proposition, producer, verifier, class, mechanism, trust root, and commit-relative timing support the claim? |
| Guarantee kind | Does the architecture support prevention, detection, recovery, attribution evidence, or a stated composition? |
| Claim-specific TCB | Which dependencies must behave correctly for this claim to hold? |
| Failure ceiling | What remains under component failure, assurance failure, compromise, reconfiguration, or partition? |

A failure ceiling is the strongest failure a mechanism still handles. EIM ownership means claim-relative technical enforcement ownership. Coverage means an authority controls all behavior whose autonomous choice can decide whether the obligation is met. The claim frame selects one eligible authority or named protocol as canonical owner; if none covers the obligation, it is unowned. For a safety obligation, coverage means every falsifying transition is constrained by the boundary or ruled out by construction. Technical accountability follows that canonical owner. Legal, business, and contractual roles remain separate facts because none of them creates enforcement control.

The canonical owner issues the guarantee. The claimant is the party relying on it, and the claim's TCB is the dependency basis for the owner's guarantee. TCB membership does not create shared ownership.

### 6.3 Delegation and the enforcement law

Delegation is not defined by handing off a function named `check` or `act`. It occurs when work or authority crosses to an independently controlled entity, creating a trust boundary and an explicit rely. Work delegation alone does not transfer ownership. If complete obligation-decisive authority transfers and the recipient becomes the canonical owner, technical accountability and guarantee issuance transfer with it. If decisive authority is only split and no named protocol owns the complete frame, the end-to-end obligation is unowned. The delegator can guarantee only the narrower obligations it still owns, such as request formation, local admission, verification, or recovery; its view of the transferred or unowned obligation is assurance.

Retaining a local check does not preserve ownership of an external outcome the delegate can independently commit, omit, duplicate, reorder, or alter. Conversely, invoking an outside mechanism is not delegation of the obligation when the local mechanism still excludes every violating outcome under the stated failure model. For a safety obligation, splitting the deciding check from the act across independent authorities leaves an open TOCTOU and interference interval unless one named protocol owns the whole commit. The EIM paper states the general Law of Non-Delegable Enforcement:

> Work delegation creates a trust boundary but does not transfer ownership while the owner's mechanism still covers every decisive outcome. Complete decisive-authority transfer moves ownership, technical accountability, and guarantee issuance. A partial split with no owning protocol leaves the end-to-end obligation unowned. The delegator can retain guarantees only for narrower obligations it still owns; its view of the transferred or unowned obligation is assurance.

The law sorts claims rather than forbidding designs. An owner can make external evidence a precondition for its local commit, but it guarantees only that local admission rule; truth, freshness, and continued validity of the external fact remain assurance. A named protocol can guarantee what its combined authority controls. A postcommit monitor and recovery mechanism can each guarantee their own procedure while supplying detection or recovery assurance about externally owned state. The EIM defines non-ordinal A0-A5 assurance classes so the exact consequence of each mechanism is stated rather than implied by the word "assured."

### 6.4 Trust anchored to claims

A check licenses a later act only while the checked condition stays true until the act commits. Whoever can change the condition or outcome during that interval is obligation-relevant to the safety claim. The atomicity bridge proves its modeled lock-protected form under its stated assumptions; a separate authority binding is required to identify the owner in a real deployment.

EIM records prevention, detection, and recovery claims, with conditions stated separately as qualifiers. Each guarantee belongs to the owner of its obligation. Other mechanisms supply assurance or own separate supporting obligations. Attribution is an evidence property that grades the detection or recovery claim relying on it. A signed receipt can bind origin under its key assumptions without proving that the external state it describes is truthful or durable, so evidence generation, custody, verification, retention, and recovery are each recorded as transitions that can themselves fulfill or violate the claim.

Trust is anchored to a claim frame, not granted once to an environment. Each frame has its own trusted computing base (TCB). For an owned frame, it contains the owner's authority base plus every other mechanism the guarantee needs. An unowned frame receives no authority-base credit. External independently controlled members are explicit relies with assurance records. The TCB marks dependency, not co-ownership, and drawing a wider boundary does not create authority. ALK authority is one subset of that TCB; host enforcement, external custodians, witnesses, cryptographic roots, and collective protocols enter the dependency record whenever the guarantee relies on them.

---

## 7. One Rule at Four Scales

The check-act rule appears at four scales in the safety research, with separate evidence at each scale.

At the structure scale, the decomposition specifications exhibit the interference window that opens when a governed check separates from its act. At the bridge scale, a parametric refinement models a lock-protected check-act-audit sequence as one fused governed transition, with six paired controls supporting the attribution and a NoLock case retained as a counterexample. At the architecture scale, EIM defines claim-relative ownership and classifies the assurance consequences of external authority. The current placement proofs classify outcomes under supplied placement and controller premises; they do not derive a real authority binding. At the system scale, an ALK places selected commits behind a mediation boundary and records which outside mechanisms stay inside the claim's TCB.

---

## 8. Synthesis: Building Real Things

### 8.1 The design procedure

Start with the required behavior, then choose the parts that can provide it.

1. Freeze the problem record. At the boundary the claim concerns, state goals, forbidden outcomes, constraints, permitted failures, and evidence requirements, without reaching for catalog names yet.
2. Classify the work (Section 5). Find its Ordering class, and for work whose dependencies form a graph apply the state-persistence test. These are facts about the work, settled before any runtime is chosen.
3. Select the execution structure (Section 4). Sequential for one ordered locus, Fork-join for sibling work resolved by a join, step graph when predecessor completion governs eligibility, stream graph when downstream work must progress while upstream stays active. Derive the expected profile at each boundary, and record a residual when nothing fits faithfully.
4. Instantiate the obligations. Select the structure and execution contracts the problem needs, choose their modes, bind the domain parameters, and identify which clauses state each primary responsibility. Connective forms supply the plumbing.
5. Map ownership and assurance (Section 6). State the complete claim frame and find which authorities cover its decisive behavior. Establish one eligible authority as the canonical owner, or record why the obligation is unowned. Then record any delegated work or authority transfer, the owner's guarantee, and the evidence for claims about external obligations. Name the trusted dependencies and the failures each claim can withstand.
6. Check adequacy and conformance. Show that the design discharges the problem record, carry each component obligation through the composed specification, and test the implementation against the resulting states and transitions to the depth the claim requires.

Starting small is guidance rather than law. Product maturity, operational constraints, and assurance requirements stay design inputs.

### 8.2 The Automation-Layer Kernel

An ALK is a reference monitor for application execution. It combines selected structure and execution contracts into one governed plan, checks their composition requirements, and records authority and trusted dependencies. It owns an obligation only when it controls all behavior decisive for that obligation. Safety commits, progress, trace relations, and evidence custody each require an authority analysis.

The services behind that boundary can run in one process, in isolated modules, on other nodes, or in external systems. Each external obligation-relevant behavior gets an EIM record naming its owner, claimant, proposition, assurance profile, remaining local guarantee, and failure ceiling, which is why a claim's TCB can be wider than the ALK's own authority. A distributed ALK owns a transition through a named collective protocol whose membership, commit rule, reconfiguration, and partition outcome are explicit.

Construction selects contracts and modes, instantiates their obligations, and checks that the parts preserve one another's clauses and meet one another's assumptions. Identity and provenance obligations enter when the application's claim requires them.

### 8.3 What the ALK evidence establishes

The machine-checked core is a semantic model, a construction theorem, four worked profiles, and a reference specification.

The model defines the registry, action and commit inventories, and the distinction between ALK authority and the claim's wider TCB. Under supplied ownership, control, provider, evidence, fairness, failure, and conformance premises, the construction theorem derives mediation of the represented actions, check-act-evidence coupling, and a guarantee ceiling set by the weakest relevant premise. It assumes the authority relationships; it does not establish deployment control or bind an issuer to each result. A worked instance shows that its premises can hold together.

The local, modular, delegated, and distributed profiles instantiate that theorem with supplied owner, assurance, failure, and TCB data. `ALK-SPEC-1` supplies a versioned reference state machine, path classification, crash and retry semantics, conformance vectors, and an API boundary. Implementation and deployment certification require further evidence.

The [ALK claim package](alk-claims.md) connects Budget and Sequential predicates and actions to controller-derived ownership, evidence, assurance, and a static certificate. Its integration example uses capacity two and two steps; the Budget safety theorem applies to any natural-number capacity. Three distinct reference-state claims check the configuration revision, predicate outcomes, owner-issued records, claimant assurance, and residuals. Legacy ceiling labels remain a compatibility projection. The certificate has no catalog-to-profile semantic refinement proof. An unsupported attempt bound produces unavailable claims.

### 8.4 The executable examples

The [Formal Examples](../formal/examples/README.md) contain twenty-two artifacts with registered claims and limits. They cover rendering, routing, scheduling, replicated JSON, transactional memory, differential-privacy accounting, CI/CD, and ten dynamic-programming algorithms. Programs return results, runtime checks, and typed structural traces. A `describe` command reports sources, construction roles, controls, limits, and falsifiers.

Rendering level-of-detail selection and route selection share `rooted_frontier`, a composition of QualityHierarchy, TraversalEngine, CompetitiveSelection, and AllocationSnapshot. Level-of-detail supplies a capacity policy under `Budget<Bytes>`; routing supplies a minimum-per-target policy that retains ties. Both route constructions are compared with a Bellman-Ford reference, and the fixture checks all 15 local-destination rows of RFC 2328's Table 2.

The Memoization family uses one composition of ResourceRegistry, TraversalEngine, and Reduction for ten dynamic-programming algorithms. Each supplies its recurrence graph, candidate derivation, reduction operation, input contract, and output projection. Separately written references check named inputs and 1,000 generated cases. Three controls bypass one shared structure at a time: the calculation still succeeds, but the recipe check must fail. A fourth corrupts the output: reference agreement must fail while the recipe check still passes.

Reconstruction requires both correct output and a classified role for every node supporting the claim. An unclassified role receives a candidate outcome for further study. The programs implement their case-study contracts; the rendering and routing examples do not implement a complete renderer or OSPF protocol.

### 8.5 LeanFormer

LeanFormer tested construction in machine learning, outside the author's prior experience. The design used the then sixteen-entry catalog to treat destructive parameter updates as shared-state mutation and the training loop as resource-governed orchestration. It combined immutable overlays, registries, budgets, staged activation, convergence control, and audit. The artifact included a governed 204-million-parameter training run; [leanformer.md](leanformer.md) reports its checks and audit records. A later reconstruction maps the unchanged design to the current catalog.

The experiment produced an implementable design and a running artifact. Comparative training efficiency was not established; later literature review found overlap with existing ML techniques. A separate B=0 diagnostic exposed an ambiguous progress signal and led to a phase-aware governor checked in a finite model.

---

## 9. The Method That Produced the Catalogs

Domain Abstraction Collapse is a five-step method, and every catalog in this paper came out of it.

1. Fix the set of systems under study and the evidence for each.
2. Describe each system's state, transitions, actors, commits, assumptions, failure cases, and obligations in its own domain vocabulary.
3. Remove the domain content while preserving behavior, interference, ordering, and promises.
4. Classify what remains into runtime givens, candidates that define obligation schemas, connective forms, and domain parameters, collapsing candidates only when behavior and responsibility survive the collapse.
5. Reconstruct each original system from the results, test representatives formally, and record every residual as a revision input.

The decomposition record shows how the source system was described in structural terms. The build recipe explains how to reconstruct it from those parts, including their interfaces and what the domain and runtime must supply. It identifies the owner of each obligation, or an ownership gap, and the mechanisms supporting assurance about external obligations. New evidence can revise either record.

---

## 10. Claims and Limits

The theory in one sentence: between ordinary computation and domain content sits a structural layer whose parts define reusable responsibilities that a system can instantiate, own, compose, and test.

The table records each claim, its evidence, and what would refute or narrow it.

| Claim | Evidence form | Evidence | What would refute or narrow it |
|---|---|---|---|
| Obligation boundary and check-act stability | Defined boundary plus machine-checked safety instance | Structure contracts, the atomicity bridge and its proof, and discriminating controls | A claimed obligation with no identifiable failure behavior, or a safety bridge or control that fails to discriminate |
| Catalog usefulness | Constructive, finite scope | Recorded mappings, reconstruction records, tested reductions, obligation placement, retained residuals, and the registered Formal Examples with their independent references and controls | A mapping that loses source behavior or obligation placement, an unexplained residual, or a faithful reduction that changes membership |
| Recurring execution structures | Machine-checked | Four complete formal chains, explicit projection, implementation refinements, distinctness witnesses, a frozen validation set, and a nested composition case | A structure that passes by leaving behavior out of its representation, an erased distinction that an obligation depends on, or a validation residual requiring revision |
| Ownership and assurance classification | Defined architecture plus machine-checked classifier | Claim-relative trust-boundary definition; parameterized placement model; assurance and partition controls; classification proof; audit-custody instance | A correctly bound counterexample to the definition, a classification failure under its premises, or evidence that the claimed controller cannot constrain the named decisive behavior |
| Composition | Machine-checked | Catalog composition theorems, a parametric assume-guarantee theorem, an exact finite-state Budget and audit instantiation with a proof of its action partition, and controls that break stated assumptions | A local invariant lost at a seam, a required rely condition omitted, an inexact action partition, or a control that fails to discriminate |
| Builder interfaces | Machine-checked at the written mappings | A common construction schema, seven kernel families, 23 derivations, paired builder contracts, an exact composition instance, an executable bridge, and package controls | A record that does not inhabit its named interface; primary-obligation identity, clause derivation status, and alternative-mode selection are not established by this row |
| ALK model and theorem | Machine-checked, conditional supplied-semantics result | The semantic model and conditional construction theorem over normalized labels and generic supplied semantics | A registered construction that violates a derived conclusion while the theorem's written premises hold; this row does not establish exact catalog-predicate instantiation, real authority, or issuer binding |
| ALK profiles | Four finite supplied-premise instances | Theorem instances with owner, assurance, failure, and TCB inputs | A profile that fails the theorem's predicates, advertises a stronger ceiling than its inputs permit, or is presented as proving deployment authority rather than instantiating supplied labels |
| ALK reference specification | Machine-checked, finite scope | Versioned state machine, conformance vectors, proof consequences, path bindings, and bridge controls | An unclassified effect path, a successful trace without its required admission, effect, evidence, or owner binding, or a mismatch with the named profile relation |
| Feasibility in an unfamiliar domain | Constructive, one case | The LeanFormer chronology, problem and decomposition records, artifact provenance, and recorded runs | Chronology showing the solution preceded the structural decomposition, a failed connection to the stripped problems, or unsupported provenance |
| Reconstruction against the current catalog | Constructive, one case | A versioned reconstruction with its reclassifications, domain functions, runtime relies, ownership seams, evidence, and residuals | An original responsibility hidden or forced into a mapping that preserves only the name, or a concealed reclassification or failed mechanism |

[formal-methods.md](formal-methods.md) provides artifact locations and runner selectors. Every catalog entry has a formal chain for its written clauses, and all 23 derivation records have refinement packages for their state and action mappings. The registry records schema and clause classifications with exact source bindings. [ALK Claims](alk-claims.md) covers the separate Budget/Sequential integration; [reference.md](reference.md) records current catalog classifications.

---

## Appendix A: Where Each Result Lives

| Component of the theory | Companion | Primary evidence there |
|---|---|---|
| The DAC method, the layer boundaries, and the parts catalog | Domain Abstraction Collapse | Survey and reconstruction method; residual discipline; complete catalog formal chains; Budget implementation refinement; minimality records |
| The LeanFormer case | [leanformer.md](leanformer.md) | Construction procedure; the six stripped problems; the B=0 episode; the measurement table; the unmeasured items |
| Connective forms and the strata model | Domain Abstraction Collapse and [reference.md](reference.md) | G v1.1 boundary, admission, promotion, and recipe accounting rules |
| Headline mappings and residuals | Domain Abstraction Collapse, [reference.md](reference.md), and [research.md](research.md) | Source mechanisms, preserved structure, omitted semantics, recipes, reclassifications, and residuals |
| The four execution structures, their profiles, and the refinement hierarchy | Execution Structures | Survey derivation; construction skeletons and builder method; complete TLA+/TLAPS/Verus chains; distinctness witnesses and refinement relations; the frozen validation set |
| The Ordering heuristic and the decision surface for graph execution | Execution Structures | Builder guidance over workload shape, progress grain, and state persistence |
| EIM surfaces and planes, ownership, assurance, and the enforcement law | The Execution Integrity Model | Obligation-schema instantiation; ownership and guarantee definitions; the atomicity bridge; placement classification and audit-custody results; the Parkerian comparison |
| ALK mediation, theorem, profiles, and reference specification | The Execution Integrity Model and the public ALK documents | Machine-checked semantic model; conditional construction theorem; four instantiated profiles; `ALK-SPEC-1` with its exact premises, failure classes, and evidence rules |
| The executable examples | [Formal Examples](../formal/examples/README.md) | Twenty-two artifacts with manifest claims and limits; the shared level-of-detail and route-selection composition; the Memoization family; five systems case studies with controls and reproduction commands |
