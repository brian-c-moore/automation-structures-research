# The Automation-Layer Kernel and the Execution Integrity Model

## An Architecture Derived from the Automation Structures

---

## Abstract

A system's guarantees depend on who controls the behavior that can fulfill or violate them. The Execution Integrity Model (EIM) traces that authority through an automated system. For each obligation, it identifies the canonical owner and the conditions under which that owner can issue a guarantee. Work delegation introduces a trust boundary. Ownership transfers only when complete authority over the decisive behavior transfers; a split without an owning protocol leaves the obligation unowned.

The model derives from Automation Structures contracts [20, 21]. It examines where work is scheduled, isolated, executed, and transported. Governance records the obligations at those surfaces; Observation records evidence about their transitions and outcomes. That evidence supports assurance for parties relying on obligations they do not own. The record also identifies trusted dependencies and failure limits. Section 3 develops this organization of the analysis.

The Automation-Layer Kernel (ALK) applies this model to an automation kernel constructed from the catalog's reusable state-machine abstractions. It acts as a domain-neutral reference monitor, combines selected contracts into a governed execution plan, and owns the obligations whose decisive behavior it controls. `alk-core` is the implementation under development, built by composing the `automation-structures` Rust library. The paper defines the architecture, its composition rules, and an analysis procedure. Sections 12 and 13 distinguish the formal results from the authority and conformance evidence still required for a deployment.

---

## 1. The architectural question

Security diagrams identify components, identities, data flows, and trust boundaries. EIM adds a question: who can control the behavior that decides each system responsibility? Organizational accountability may sit with one party while a scheduler, policy service, broker, store, or cluster protocol controls the relevant behavior.

Start with one concrete obligation. State what must hold for its subject, how far the claim
extends, and which failures it includes. Then identify the behavior that can determine whether it
holds and who controls that behavior. Any dependency the claim relies on must be explicit.

Different obligations require different analyses. A capacity limit can be violated by one
allocation. Eventual completion depends on progress and fairness over an execution history.
An evidence obligation depends on how a record is created, kept, and verified. Retention continues
to depend on custody after creation succeeds. Section 10 follows these questions through a
Kubernetes audit path.

An obligation can require several formulas to express and prove. EIM connects those formulas to
the same responsibility in the architecture. ALK applies the analysis to an execution system
that mediates selected obligations.

---

## 2. Research basis and derivation method

### 2.1 Evidence roles

The argument uses distinct sources for distinct purposes.

| Evidence role | Source | Use in this paper |
|---|---|---|
| Structure derivation | Automation Structures catalog, contracts, TLA+ specifications, TLAPS proofs, controls, and refinement records [20, 21] | Supplies reusable responsibilities and the clauses currently used to formalize them |
| Placement semantics | Atomicity bridge and ALK/EIM placement corpus [21] | Connects fused check-act-audit transitions to ownership and evidence placement |
| Security architecture | Anderson's reference monitor, Saltzer and Schroeder's protection principles, NIST's TCB definition, and NIST systems security engineering [2, 7, 9, 11, 12] | Grounds mediation, trusted dependency, trustworthiness, and assurance terminology |
| Composition and distribution | Abadi and Lamport, Herlihy and Wing, Lamport's Paxos, and Gilbert and Lynch [1, 3, 5, 6] | Grounds rely/guarantee composition, linearization, collective commit, and partition outcomes |
| Evidence systems | NIST log management, Haber and Stornetta, Certificate Transparency, and the `AuditSink` corpus [4, 13, 14, 21] | Grounds generation, custody, integrity, witnessing, and asynchronous verification distinctions |
| Practitioner method | Microsoft SDL threat modeling and STRIDE [15] | Supplies the precedent for a repeatable architecture-analysis instrument |

These labels keep the paper's claims aligned with that evidence.

| Label | Meaning |
|---|---|
| `TLC-CHECKED` | Explored by the named state-machine configuration at finite bounds |
| `TLAPS-PROVED` | Proved under stated assumptions |
| `VERUS-VERIFIED` | Verified for the named executable contract |
| `DERIVED` | Obtained by projection, instantiation, composition, or logical consequence from recorded contracts |
| `DEFINED` | A term or classification introduced to make the architecture analyzable |

A proof establishes a statement about its model. Applying it to a system also requires evidence that the model represents the relevant obligation, authority, behavior, and failures. Section 12 identifies which of those connections the current artifacts establish.

### 2.2 The Automation Layer, contracts, and obligation instances

The Automation Layer contains reusable structures that govern computation. Domain bindings supply the values, functions, and policies those structures use.

| Stratum | Contribution |
|---|---|
| Mathematical and computational substrate | State machines, graphs, orders, functions, algorithms, concurrency, and general execution mechanisms |
| Automation Layer | Obligation-bearing structures, connective forms, execution structures, composition rules, ownership, mediation, and evidence semantics |
| Domain instantiation | Domain types, scoring or aggregation functions, policies, protocols, effects, resources, and desired outcomes |
| Deployment realization | Operating-system and hardware mechanisms, clocks, storage, networks, external services, and their failure behavior |

The first three rows describe abstraction levels. Deployment mechanisms realize them and enter the analysis through implementation mappings and runtime assumptions. Section 13 states the catalog's current scope.

Each obligation-bearing structure defines a reusable contract:

$$
Schema(S) = \langle Responsibility, Modes, Clauses, Parameters, Assumptions, Form, Concern \rangle
$$

The responsibility is what a system using the structure must preserve or achieve. Modes hold
alternative contracts, not cumulative requirements. Clauses are the exact predicates and temporal
properties that specify the responsibility. Parameters and assumptions say what the domain and
environment must supply. Form records whether a clause is safety, liveness, or relational. Concern
records what it governs, such as capacity, ordering, integrity, custody, progress, or evidence.

Several clauses may specify one responsibility. Supporting facts about types or representations
help the proof without creating new obligations; the same applies to assumptions, helper
invariants, and derived corollaries. For each primary obligation schema, the record identifies
the exact contributing formulas and the proofs that establish them. It also records their
parameters, assumptions, and derivation status.

A system creates the concrete obligation by instantiating that contract:

$$
O = Instantiate(Schema(S), X, Mode, Scope, FailureModel)
$$

The instance then records the behavior that can decide the obligation, the authority boundary,
and the relevant relies. Ownership and guarantee kind are derived from that authority; they are
not properties stored in the reusable catalog contract. For safety, Herlihy and Wing's
linearizability supplies the familiar single-commit case, and the atomicity bridge applies it to a
governed check, act, and audit sequence [5, 21]. Other property forms require their own decisive
behavior.

An automation subject selects structure contracts and execution contracts separately, chooses one
mode where alternatives exist, and instantiates only what it uses. Runtime closure adds the
obligations created at their seams, and the claim adds any identity semantics it names:

$$
\Omega_{ALK}(X) =
  Instantiate_X(SelectedStructureSchemas)
  \cup Instantiate_X(SelectedExecutionSchemas)
  \cup \Omega_{composition}(X)
  \cup \Omega_{placement}(X)
  \cup \Omega_{mediation}(X)
  \cup \Omega_{identity}(X)
$$

Each added set is defined by its content. $\Omega_{composition}(X)$ holds assumption
discharge and preservation across seams. $\Omega_{placement}(X)$ holds ownership and
assurance for externally controlled decisive behavior. $\Omega_{mediation}(X)$ holds
mediation of the transitions included in the claim. $\Omega_{identity}(X)$ holds stable
identity and provenance when the claim names them. Sections 5, 6, and 11 formalize that closure.

### 2.3 Catalog obligation schemas

The table summarizes catalog responsibilities. The registry classifies 69 clause occurrences into 36 obligation schemas; several clauses may support one obligation. The repository index records current membership and artifact locations.

| Catalog entry | Decisive behavior | Schema contribution |
|---|---|---|
| `Budget` | Admission and accounting against capacity | Preserve the ceiling and every ledger transfer across allocated, reserved, and pending-eviction quantities |
| `QualityHierarchy` | Parent-child and quality-metadata mutation | Preserve parent agreement and strict level order; derive acyclicity from strict descent |
| `ResourceRegistry` | Register, deregister, lookup, and upsert | Expose one committed mapping, preserve unaffected bindings, and commit upserts atomically |
| `CompetitiveSelection` | Allocation under the selected competition mode | Preserve exclusion or allocation within capacity, live-score eligibility, ordering, and deterministic tie policy for the selected mode |
| `ActuationPass` | Side-effect commit against a live allocation | Apply only within the accepted scope, preserve resource fidelity, and report truthful completion |
| `PropagationPass` | Local graph update with a declared round limit | Preserve neighbor locality and round-start isolation; settle at a fixed point or the declared ceiling under the liveness rely |
| `ConvergenceGovernor` | Convergence lifecycle transition | Require recorded history for cooling or convergence and preserve the allowed phase relation |
| `AuditSink` | Creation of audit evidence | Preserve chain and tail consistency with content binding under the declared hash and anchor assumptions |
| `BacktrackingTraversal` | Paired mutation and checkpoint pop | Preserve do-undo pairing, restoration, checkpoint order, and sound recorded leaves |
| `AllocationSnapshot` | Fused acceptance and budget update | Keep accepted membership consistent with its charged cost and remaining capacity |
| `FederatedBudget` | Capacity carve, consume, return, and reassignment | Preserve master and subpool ceilings together with conservation of carved capacity |
| `Bisection` | Probe against a monotone boundary | Preserve interval containment, contraction, probe ceiling, and fair convergence under domain-fit assumptions |
| `EquivalenceClass` | Parent and rank mutation | Preserve representative validity and parent/rank path consistency |
| `RateLimit` | Admission in a runtime-supplied clock window | Preserve the per-window ceiling and ordered clock/window state |
| `Reduction` | Atomic consume-and-advance over an ordered stream | Keep the result equal to the exact consumed-prefix fold |
| `RelationshipGraph` | Edge mutation and adjacency projection | Preserve edge/adjacency agreement and the selected loop policy |
| `Sampler` | Draw against live support and a sample bound | Keep selected items inside current support and within the declared bound |
| `Signal` | Notification bookkeeping after state change | Restrict delivery to registered pending work and keep pending and delivered states disjoint |
| `TraversalEngine` | Frontier transition and visit acceptance | Keep accepted nodes tied to visits and account accepted cost against the visit budget |

For the fixed-cost root-star profile, the `TraversalEngine` TLA+ contract proves both
accepted-subset validity and exact accounting: the initial budget equals the remaining budget plus
two units for each accepted node. This is state-safety evidence. It does not establish that queued
work eventually runs, that the frontier drains, or that the traversal visits every eligible node.

### 2.4 Obligation concern families

Several entries address the same engineering concern at different decisive behaviors. The
following families are navigation tags. They do not merge obligations or prove equivalence.

| Obligation family | Characteristic violation | Principal structures |
|---|---|---|
| Admission within declared limits | A commit admits work beyond a declared limit | `Budget`, `RateLimit`, `AllocationSnapshot`, `FederatedBudget`, `Sampler`, `TraversalEngine` |
| Conservation and accounting | State transfers create, lose, misassign, or double-count governed quantity | `Budget`, `AllocationSnapshot`, `FederatedBudget` |
| Authoritative association | Two views disagree about identity, membership, parentage, or relation | `ResourceRegistry`, `QualityHierarchy`, `EquivalenceClass`, `RelationshipGraph` |
| Eligibility and resolution | An ineligible candidate wins or equivalent candidates resolve inconsistently | `CompetitiveSelection`, `Sampler`, `Bisection`, `TraversalEngine` |
| Scope and fidelity | An effect reaches the wrong subject, resource, neighbor, or snapshot | `ActuationPass`, `PropagationPass` |
| History and ordering | A transition lacks the history or order that licenses it | `ConvergenceGovernor`, `AuditSink`, `BacktrackingTraversal`, `Reduction`, `Signal` |
| Progress and truthful closure | Work stalls, escapes its bound, or reports closure before its obligation is met | `ActuationPass`, `PropagationPass`, `Bisection`, `Signal`, `TraversalEngine` |
| Restoration | Reversal fails to recover the recorded pre-action state | `BacktrackingTraversal` |
| Evidence binding | Evidence can be reordered, detached from content, or detached from the governed commit | `AuditSink`, `Reduction`, `AllocationSnapshot` |

---

## 3. Deriving the Execution Integrity Model

### 3.1 Execution surfaces and cross-cutting planes

Four surfaces group the places where execution changes: Scheduling, Isolation, Execution, and Transport. Governance states what must hold; Observation records the evidence.

| EIM term | Structural derivation | Automation question |
|---|---|---|
| Scheduling | Admission within declared limits, eligibility, dependency relations, progress, phase history, and execution-structure selection | Which work becomes eligible, receives capacity, starts, pauses, retries, or terminates? |
| Isolation | Authoritative state association, partitioned capacity, effect scope, resource fidelity, and mediated access | Which subject can observe or mutate which state and resource? |
| Execution | Authoritative module association, provenance, resource use within declared limits, effect fidelity, restoration, and truthful completion | Which logic commits which effect under which identity and constraints? |
| Transport | Relationship graphs, endpoint registries, queues with capacity limits, rate limits, signals, ordering, and evidence | Which declared path can carry a message with which delivery, order, and flow semantics? |
| Governance | The instantiated obligations over every execution surface | What must the system preserve or achieve? |
| Observation | Evidence about governed commits and trace outcomes, then transported, protected, retained, reconciled, and retrieved | Which claim can the evidence support, at what time, under whose custody? |

Scheduling through Transport are surfaces because each identifies a class of automation
transition. Governance and Observation are planes because each crosses those surfaces. For
automation subject `X`:

$$
Governance(X) =
\bigcup_{r \in \{Scheduling, Isolation, Execution, Transport\}}
Obligations(X,r)
$$

$$
Observation(X) = Evidence\left(
Transitions(Governance(X)) \cup TraceOutcomes(Governance(X))
\right)
$$

Governance includes capacity, association, selection, isolation, provenance, transport, and restoration obligations. Observation creates and protects evidence about their transitions and outcomes.

### 3.2 Residual mechanisms

The catalog describes governed automation structure. Lower-layer mechanisms supply part of
the realization. Memory protection, process credentials, capability enforcement, clocks,
durable media, cryptographic keys, and network delivery enter the analysis as trusted
interfaces or environmental relies. An ALK can own the automation-level transition that invokes
them while the host, hardware, key service, or network owns the lower-layer transition.

This separation keeps the surfaces useful. Isolation names the subject's access and
effect boundaries; the host supplies enforcement mechanisms beneath that boundary. Execution
names authorization, provenance, resource, and effect obligations; an interpreter, runtime,
operating system, and processor realize the instruction path. The claim-specific TCB in
Section 7 records each dependency.

### 3.3 EIM as a practitioner instrument

Threat modeling asks how a component or flow can be attacked. EIM asks which authority can uphold the affected obligation and what assurance remains when authority crosses a boundary. The two analyses can be used in the same review [15].

The Parkerian Hexad supplies an independent security-attribute review [8]. Confidentiality maps
to access and scope obligations; integrity maps to authoritative association, fidelity, and
evidence binding; availability maps to admission, progress, and transport; possession maps to
custody and resource authority; authenticity maps to identity, provenance, and signed
evidence; utility maps to correct order, scope, and execution result. Derivation remains with
the structure corpus. The Hexad checks the resulting map from a security-attribute
perspective.

---

## 4. The EIM analysis procedure

An EIM review produces an obligation and assurance map for a declared automation claim.
The procedure follows these steps.

1. Define the automation subject, claimant, operational scope, protected claim, and failure
   model.
2. Select the structure and execution contracts, their modes, and the primary obligation schemas
   required by the claim.
3. Bind every obligation to its exact clauses, domain parameters, assumptions, and failure model.
4. Enumerate every action, omission, scheduling choice, trace relation, evidence step, and custody
   step that can decide each obligation.
5. Assign the authority or collective protocol controlling all of that decisive behavior.
6. Mark each independently controlled portion as delegation and record the exact assurance
   mechanism and timing.
7. Compute the guarantee kind, claim-specific TCB, failure cut sets, and partition outcome.
8. Test mediation bypass, unmediated execution, assurance failure, stale evidence, recovery
   failure, reconfiguration, and correlated compromise.

The working record is compact:

| Field | Required content |
|---|---|
| Claim anchor | Automation subject, obligation, scope, claimant, and failure model |
| Runtime relies | Provider, exact supplied semantics, failure behavior, trusted dependency, and boundary where the facility is assumed |
| Decisive behavior | Safety commits, progress actions, trace relations, evidence custody, or other behavior whose autonomous choice can determine the obligation |
| Enforcement owner | Authority or named protocol controlling all decisive behavior at the anchored boundary |
| Delegation boundary | Independent authority receiving obligation-relevant control and the behavior that crossed |
| Assurance | Claimant, proposition, A0-A5 profile, evidence producer, verifier, timing, independence, and trust roots |
| Owned claim | Owner-issued prevention, detection, recovery, or stated composition, with the attribution evidence it relies on |
| TCB | Sufficient dependency basis for the anchored claim; minimality is separate |
| Ceiling | Outcome under component failure, assurance failure, compromise, or partition |

The procedure ends with an architecture statement a reviewer can test. It replaces a generic
box labeled "logging," for example, with separate ownership rows for event creation,
transmission, durable custody, retention, integrity, retrieval, reconciliation, and recovery.

### 4.1 Unmediated executors

An unmediated executor is any path that schedules, advances, retries, resumes, completes, or
commits a governed unit of work outside its declared ALK mediation transition. The term concerns
execution authority and is distinct from observational side channels such as timing, cache, or
power leakage.

Common sources include a library-owned worker pool, embedded asynchronous runtime, callback loop,
parallel query engine, foreign task scheduler, background retry service, device queue, or helper
process. Calling such a facility from mediated code does not make its later transitions mediated.
The EIM record must determine whether the facility performs synchronously on the execution resource
the ALK assigned, creates or enlists another execution resource, or owns an explicitly external
commit. A library's internal parallelism remains a separate execution path even when its public call
returns synchronously.

For an ALK profile claiming complete execution mediation, admitted code may compute synchronously
on its assigned execution resource but may not independently create threads, tasks, workers,
callbacks, device submissions, or other governed work. An external executor is not a hidden side
channel when the ALK mediates its submission and result boundary, the far-side execution lies
explicitly outside the governed universe or has a named owner, and the guarantee ceiling states what
the ALK cannot prevent. Otherwise the path is a bypass and defeats the complete-mediation claim.

---

## 5. Ownership, delegation, and the enforcement law

### 5.1 Claim-relative enforcement ownership

[Claim-Relative Ownership and Assurance](claim-relative-ownership.md) owns the common definition.
The word owner in EIM means the canonical technical enforcement owner for one claim frame, not
legal title, possession, authorship, or responsibility for paying a vendor. The frame fixes the
subject, obligation, mode, scope, observation boundary, authority boundary, claimant, failure model,
abstraction, lifecycle phase, and property form. EIM calls the property-specific behavior whose
autonomous choice can determine whether the obligation is met "obligation-decisive".

Coverage makes a principal eligible; it does not itself confer ownership or make every technically
capable boundary an issuer. The claim frame identifies one eligible principal as technically
accountable, or records the obligation as unowned. A named protocol is one principal at its protocol
frame, while its participants may own distinct obligations in other frames:

$$
Owner(F) \in Principal \cup \{\bot\},
\qquad Owner(F)=P \Rightarrow Covers(P,F)
$$

The value `⊥` records an unowned obligation. Technical accountability for the claim follows
`Owner(F)` and cannot be delegated separately. Legal, business, and organizational accountability
remain separate roles and must not be used as evidence of technical control.

Ownership therefore depends on the obligation and perspective. An authority may own request
formation but not the requested external effect, evidence creation but not evidence retention, or
local admission but not eventual progress. Expanding the claim boundary can name a larger protocol
as owner only when that protocol covers the larger decisive behavior. Drawing a wider box
does not give the original delegator control.

For claim frame `F`, authority boundary `B`, and a safety obligation, coverage is binary:

$$
Covers_B(F) \iff
\forall t \in ViolatingTransitions(F.Obligation):
CommitAuthority(t) \subseteq B
\;\lor\;
ExcludedByConstruction_B(t,F.FailureModel)
$$

For safety, an eligible boundary must commit or exclude every transition that can falsify the obligation. The atomicity bridge's fused check-act transition is one such mechanism. A local check, telemetry access, or contractual role alone does not establish that control.

Execution authority follows the same rule. A library or runtime invoked inside `B` does not enter
the authority boundary merely because the initial call was mediated. If its worker, reactor,
callback, retry loop, or device queue can later advance governed work or commit a violating
transition outside `B`, that path must be excluded, mediated as a distinct ALK transition, or
recorded under its actual external owner.

Ownership is also granular. A component may own audit-event creation and chain extension,
while an external store owns durable custody and retention. Treating "audit" as one
responsibility hides that transfer. EIM splits it at the commits.

Liveness ownership records the authority over progress actions together with scheduler,
fairness, clock, and availability relies. A stalled trace may lack a single falsifying commit.
Its guarantee follows the temporal contract.

Confidentiality and noninterference can require relations over multiple possible traces rather
than one falsifying transition. EIM can locate the authorities and relies involved, but the
transition-ownership rule below does not by itself establish such relational properties.

### 5.2 Delegation

Work delegation occurs whenever an independently controlled authority receives work, access,
possession, or a capability with explicit limits. It creates a trust boundary and therefore an explicit rely or
assurance record. It does not by itself transfer ownership. Ownership transfers only when complete
authority over the obligation-decisive behavior transfers and the recipient covers the obligation.
Calling a library, worker, or device leaves ownership unchanged when the caller's mechanism still
constrains every violating outcome within the failure model. Conversely, retaining a local check
does not preserve ownership of an external effect that the delegate can commit, omit, reorder,
duplicate, or alter independently.

For the safety specialization, delegation occurs when a transition
$t \in ViolatingTransitions(O)$ commits under authority `D` outside `B`:

$$
Delegate_{B \rightarrow D}(F,t) \land \neg ExcludedByConstruction_B(t,F.FailureModel)
\Rightarrow \neg Covers_B(F)
$$

The implication follows from the coverage definition: the transition can falsify the obligation, its authority is external, and `B` does not exclude it. Behavior outside `Decisive(F)` may add a rely without transferring ownership. Technical accountability follows the canonical owner.

After delegation, the parties can own different obligations. The delegator can guarantee its own
request formation, admission rule, verification procedure, or recovery procedure when it controls
those behaviors. The delegate can guarantee the externally committed effect or state it controls.
From the delegator's perspective, the delegate's statement and evidence are assurance. A named
protocol that governs all decisive behaviors can be the owner at that abstraction; its participants
are dependencies of that guarantee, not independent issuers of the same claim.

When independently controlled parties split a check from the act and no protocol owns the whole
interval, neither party owns the end-to-end safety obligation. The checker can guarantee that it
checked a proposition at a time. The actor can guarantee only what its own authority covers. The
unowned interval is a trust gap.

### 5.3 Law of Non-Delegable Enforcement

The general Law of Non-Delegable Enforcement is:

> Technical accountability cannot be delegated independently of ownership. Delegating a defined task
> leaves ownership with the canonical owner while its mechanism still covers every decisive outcome.
> Transferring complete decisive authority transfers ownership and technical accountability. Splitting
> decisive authority without one owning protocol leaves the end-to-end obligation unowned. A former
> owner's claim about an obligation it no longer owns is assurance.

For a safety obligation `O`, declared authority boundary `B`, governed transition `t`, and
delegate `D`, the transition form is:

> If `t` can falsify `O`, `D` commits `t` outside `B`, and no mechanism controlled
> by `B` constrains `t` before its commit, then `B` cannot issue a prevention guarantee
> for `O` solely from behavior inside `B`.

External evidence can be a precondition for a local commit. The local owner guarantees that admission rule; truth, freshness, and continued validity of the external fact remain assurance. A monitor or recovery service may own a separate detection or restoration obligation. A protocol may own the complete obligation when it controls all decisive behavior.

Schneider's execution-monitor work characterizes the safety policies enforceable by halting
an execution before a bad prefix extends [10]. The law above asks the corresponding placement
question: which authority can halt the governed transition before its commit?

### 5.4 Check-act stability

For safety obligations, the law includes the check-act rule. A check licenses an act only while the
checked predicate remains stable under permitted interference until commit:

$$
P(s_{check}) \land Stable(P, Interference, [check,commit])
\Rightarrow P(s_{commit})
$$

The Automation Structures atomicity bridge proves that its modeled lock-protected check-act-audit
sequence refines a fused governed transition. Its controls demonstrate the represented failures
when the act or audit escapes the interval. The bridge does not identify a real deployment owner by
itself. Delegation introduces an independent authority into the interval; the authority binding
must show whether that party can change the checked fact, the act, or the evidence before the
relevant commit.

---

## 6. Assurance as a separate architecture

### 6.1 Guarantee kinds

Assurance supplies evidence, a constraint, or a recovery premise to the owner. It does not issue
the guarantee for an obligation it does not own. Its position relative to commit determines what
the owner can guarantee and what separate obligation the assurance provider may itself own.

| Assurance position | Mechanism form | Owner guarantee supported | Dependency consequence |
|---|---|---|---|
| Before commit | Required receipt, quorum certificate, policy token, or independent witness | The owner can guarantee that its commit will not proceed without the required evidence. The external fact remains assurance unless the provider participates in the owning commit protocol. | Assurance producer and verifier enter the prevention TCB |
| At commit | Transactional co-commit or threshold authorization at a shared linearization point | The protocol that owns the fused commit can guarantee prevention. | Commit protocol, membership, and keys enter the prevention TCB |
| After commit | Reconciliation, retrieval test, consistency proof, or monitor comparison | The monitoring owner can guarantee its detection procedure. Its report is assurance about the externally owned state. | Monitor, clock, evidence source, and response path enter the detection TCB |
| After loss | Replica, escrow, replay log, checkpoint, or independent copy | The recovery owner can guarantee its restoration procedure under the named custody premises. | Recovery authority, replica independence, and restoration procedure enter the recovery TCB |
| Across the record | Signature, hash chain, published head, or external timestamp | The evidence owner can guarantee origin and integrity under its key and custody premises. Truth about another owner's state remains assurance. | Key roots, anchor, verifier, and availability of evidence enter the TCB of the guarantee that relies on them |

Prevention, detection, and recovery are guarantee kinds attached to their owning obligations. The
same mechanism can guarantee the obligation it owns while supplying assurance to the owner of a
different obligation. Attribution is an evidence property: it strengthens the detection or
recovery guarantee that relies on it, and it takes its obligations from `AuditSink` under the
hash, key, and custody assumptions of the evidence structure. A detection mechanism satisfies an
architecture whose stated objective is timely detection. It supports a different claim from
precommit exclusion.

### 6.2 What evidence establishes

A signed response establishes origin and integrity under its key assumptions. Truthfulness
about external state remains a separate trust assumption. A content hash supports comparison
with known content; current possession and availability require custody or retrieval evidence.
A successful retrieval confirms availability at the observation time. Continuous retention
depends on the custodian, its controls, and any independent witness or replica.

Certificate Transparency supplies a researched example of these distinctions [14]. A signed
certificate timestamp is a log's promise to include an entry; a later proof of inclusion and
consistency supports detection of incorrect operation. RFC 9162 also identifies split views as
a condition requiring trust in the log or additional consistency mechanisms. The protocol
therefore demonstrates how asynchronous evidence can create strong detection and attribution
while the log remains the owner of its append commit.

### 6.3 Assurance classes and profiles

Assurance is justified confidence in another owner's proposition. It is always indexed by the
claimant, proposition, source, observation time, failure assumptions, and evidence path. The same
fact can be a guarantee from its owner and assurance to everyone outside that owner's enforcement
boundary.

The classes below are practitioner shorthand for the exact consequence of common mechanisms. They
are not a single strength ladder: detection, recovery, attribution, and prevention answer different
questions. An assurance profile is a set such as `A1 + A3(delta=5m) + A4(RPO=1h,RTO=4h)`, not
merely the largest number present.

| Class | Minimum mechanism | What the claimant may be assured of | What is not established |
|---|---|---|---|
| A0 - reliance only | Request, configuration, or contract with no result evidence | Only the claimant's own request or expectation | External acceptance, truth, execution, state, or durability |
| A1 - attributed assertion | Authenticated response, signed receipt, or attestation bound to identity and subject | The named source asserted the proposition represented by the evidence | Truth, completeness, freshness, durability, or continuing validity |
| A2 - point observation | Independently performed read-back, retrieval, comparison, or verification at time `t` | The verifier observed the stated property at the named observation point | The property before or after `t`, or stability between a check and later act |
| A3 - detection within a stated time | Independent monitor or witness with stated coverage, clock, evidence source, and bound $\Delta$ | A covered divergence will be detected or attributed within $\Delta$, under the stated assumptions | Prevention, zero exposure, or resistance to correlated monitor/source failure |
| A4 - recovery with stated time and data-loss limits | Independent copy, escrow, replay log, or checkpoint with tested restore and declared RPO/RTO | Covered state can be restored to the stated recovery point within the stated time, under the custody assumptions | Continuous correctness, uninterrupted availability, or recovery of unrecorded effects |
| A5 - owner/protocol backed | Named external owner or protocol, decisive-authority binding, issued guarantee, failure ceiling, and evidence binding the result to the claim | The external owner guarantees the stated obligation under its relies and ceiling | Ownership by the claimant; truth beyond the protocol model; protection outside the stated failure ceiling |

Independence is an explicit dimension. Evidence produced and verified by the same authority is
self-attestation even when cryptographically authentic. Adding an independent verifier changes the
correlated-failure assumptions, but does not automatically supply detection bounds, recovery, or
prevention.

### 6.4 Assurance patterns

The placement model distinguishes precommit constraints, postcommit detection, and recovery after loss. The patterns below apply that distinction. Each use requires a specific failure model, provider contract, and evidence.

| Pattern | Structural reading | Principal question |
|---|---|---|
| Precommit receipt | Evidence becomes an admission predicate | Does the receipt attest durable acceptance or only request receipt? |
| Independent witness | A second authority observes or co-signs the transition | Which correlated failures remain? |
| External anchor | A chain head crosses into separate custody | How often can the writer rewrite history before anchoring? |
| Reconciliation | Two authoritative views are compared after commit | What is the maximum exposure and who acts on divergence? |
| Replicated custody | Independent copies preserve recovery material | Are failures and administrative authorities sufficiently separated? |
| Threshold authority | A quorum or threshold signature licenses commit | Which membership and key failures can violate safety or stop progress? |
| Partitioned authority | A global obligation is divided into conserved local shares | How are shares carved, returned, and prevented from duplication? |
| Recovery escrow | A separately controlled artifact can reconstruct state | Which state, ordering, freshness, and completeness guarantees survive restoration? |

### 6.5 Consequences of an open trust boundary

The failure modes depend on which authority crosses the trust boundary.

| Delegated authority | Local guarantee that can remain | Assurance needed for the delegated obligation | Gap exposed when unstated or stale |
|---|---|---|---|
| Condition evaluation or authorization | The local party used the returned result according to its rule | Accuracy, subject binding, freshness, and stability until use | TOCTOU, stale authorization, confused subject, race condition |
| External effect or state commit | Request formation, local admission, and local record creation | Effect fidelity, uniqueness, ordering, atomicity, completion, and authoritative result | Lost, duplicate, partial, reordered, or misdirected effects; data-integrity failure |
| State custody or retention | Local transfer and any independently retained copy | Existence, content integrity, durability, availability, retention, and deletion behavior | Silent corruption, data loss, rollback, split view, or false deletion claim |
| Scheduling or progress | Local eligibility and dispatch decisions | Fairness, capacity, retry, timing, terminal-state truth, and availability | Stall, starvation, retry storm, late completion, or closure race |
| Evidence creation, custody, or verification | Locally controlled portion of the evidence path | Completeness, truthfulness, binding, immutability, retention, and verifier correctness | Audit gap, false attribution, rewritable history, or unverifiable outcome |
| Check and act split across independent authorities | Each party's own local procedure | An owning protocol or explicit A1-A5 profile for the end-to-end claim | Unowned interval, TOCTOU, interference race, and inconsistent views |

For each mechanism, record the supported proposition, assurance class, trust roots, and failures it covers.

### 6.6 Obligation-assurance graph

An obligation-assurance graph records the dependencies:

$$
G_O = (V, E, \tau, \gamma)
$$

The nodes `V` are obligations, owners, delegates, evidence producers, verifiers, recovery
authorities, and trust roots. The edges `E` are `owns`, `delegates-to`, `commits-through`,
`attests`, `witnesses`, `reconciles`, `recovers-from`, and `relies-on`. Function
$\tau$ places each edge before, at, or after commit. Function $\gamma$ labels its
prevention, detection, or recovery contribution and the attribution evidence it supplies.

The graph identifies the owner, TCB, supported guarantee, and combinations of dependency failures that defeat it. It also makes dependencies between external services explicit. Proving the TCB minimal requires a separate reduction.

---

## 7. Trusted computing bases anchored to claims

### 7.1 Claim frame

NIST defines a TCB as the totality of protection mechanisms responsible for enforcing a
security policy [11]. NIST systems security engineering also treats assurance,
trustworthiness, validation, and verification as related engineering concerns [12]. The TCB
set becomes useful for automation architecture when attached to a claim frame:

$$
F = \langle Subject, Obligation, Mode, Scope, ObservationBoundary,
AuthorityBoundary, Claimant, FailureModel, Abstraction,
LifecyclePhase, PropertyForm \rangle
$$

The claimant matters because trust is a relation. A system operator, application owner, customer,
regulator, external auditor, and workload tenant can accept different roots and failure
assumptions for the same mechanism. In the formal models, `GuaranteeClaimant` records this relying
party; it does not identify the owner that issues the guarantee. The other fields prevent a change
of perspective, abstraction, lifecycle phase, or property form from silently changing the ownership
answer.

### 7.2 Claim-specific TCB

For frame `F` and guarantee `g`, distinguish the owner's authority mechanisms from the
complete dependency base:

$$
AuthorityBase_g(F) \subseteq ClaimTCB_g(F)
$$

$$
ExternalRelies_g(F) = ClaimTCB_g(F) \setminus AuthorityBase_g(F)
$$

`AuthorityBase` contains the mechanisms governed by the canonical owner. That owner can itself be a
named protocol.
`ExternalRelies` contains independently controlled mechanisms or propositions whose correct
behavior the claim assumes. Every external rely names its owner or remains an explicit gap, together
with the assurance basis available to the claimant. TCB membership records dependency, not shared
ownership.

The analysis can later ask whether a dependency set is inclusion-minimal:

$$
Minimal_g(D,F) \iff
Sufficient_g(D,F) \land \nexists E \subset D : Sufficient_g(E,F)
$$

Minimality receives proof credit only when a separate reduction result establishes `Sufficient`
for the retained set and its proper subsets. Alternative quorum configurations, witnesses, or
recovery architectures may produce incomparable sufficient sets without changing the canonical
owner of one fixed claim frame.

The subject view is the union of its anchored TCBs:

$$
TCB_{Subject} =
\bigcup_{F \in ClaimFrames(Subject),\;g \in Guarantees(F)} ClaimTCB_g(F)
$$

Per-frame views remain primary because the union can obscure why a dependency is trusted. One
external store may enter the retention TCB while remaining outside the TCB for workload admission.
One host clock may enter rate-limit and ordering claims while remaining irrelevant to content
provenance.

### 7.3 ALK authority and subject TCB

The ALK authority boundary and the subject TCB answer different questions. The authority base
identifies the mechanisms governed by the canonical owner. The TCB is the complete dependency
boundary of that owner's guarantee:

$$
AuthorityBase_{ALK}(F) \subseteq ClaimTCB_g(F)
$$

The ALK owns the automation-level obligations whose complete decisive behavior it commits or
excludes. The TCB can also contain the host kernel, processor, runtime, cryptographic roots,
external custodians, witnesses, or cluster protocol when the guarantee requires their correct
behavior. An independently controlled member remains an external rely even if an architecture
diagram draws it inside a larger system box. A user-space ALK can therefore own workload admission
while relying on the operating system for process isolation. The admission and isolation obligations
receive different frames, owners, guarantees, and assurance records.

A useful TCB statement names the claim and dependencies: for example, audit retention may rely on an object store, retention-policy authority, credential root, and retrieval verifier under regional-loss and administrator-compromise assumptions.

---

## 8. The Automation-Layer Kernel

### 8.1 Definition

An Automation-Layer Kernel is a domain-neutral reference monitor for a declared set of execution behaviors. It combines selected structure and execution contracts into one governed plan, checks their composition requirements, and maps authority and trusted dependencies. It owns obligations whose complete decisive behavior it controls and produces evidence at the governed boundary. Domain bindings supply functions, policies, protocols, effects, and resources.

Reference-monitor and operating-system research supplies the architectural criteria. Anderson requires tamper resistance, invocation on governed references, and a size suitable for analysis. Saltzer and Schroeder add complete mediation, least privilege, fail-safe defaults, and economy of mechanism. Liedtke's microkernel work supports separating privileged mechanism from service policy [2, 7, 9]. The structure corpus supplies the contracts enforced behind the mediator.

The kernel boundary follows enforcement authority. Services may run in the same process, isolated modules, other nodes, or external systems; EIM records the owner and assurance for each claim.

Trust zones, module ABIs, plugins, control planes, isolation mechanisms, and deployment topology are implementation choices. They enter the analysis when a claim depends on them.

### 8.2 Required architectural properties

An ALK claim records these properties:

1. The automation subject, managed workloads, governed state, and protected resources have
   stable identities.
2. The kernel core remains domain-neutral; domain functions and effects enter through declared
   bindings with explicit authority.
3. Every workload-level scheduling, dispatch, continuation, retry, resume, completion, and effect
   transition included in the claim passes through a declared mediation point.
4. No embedded runtime, worker pool, callback loop, helper process, device queue, or foreign
   scheduler can advance governed work through an unmodeled path.
5. For safety obligations using a separated check and act, the checked predicate remains stable
   until the transition's linearization point.
6. Component assumptions are discharged by peer guarantees or named trusted interfaces.
7. Composed transitions preserve constituent invariants under stated interference and
   failure assumptions.
8. Significant commits create evidence whose content and ordering are bound to the governed
   transition.
9. Delegated obligation-relevant behavior exposes the trust boundary, external owner, claimant,
   exact assurance profile, remaining local guarantees, and failure ceiling.
10. Cluster commits expose membership, protocol, quorum or share rule, reconfiguration, and
   partition outcome.

Complete mediation is claim-relative. For a profile claiming that all workload-level execution
flows through the ALK, code may compute synchronously on its assigned execution resource but may not
create, schedule, advance, retry, resume, or complete work on another resource except through the
ALK. A direct database credential, debug port, shared-memory path, library-owned executor,
background callback, host administrator write, or similar path is either excluded by construction
or enters the modeled transition set under its actual owner. The threat model tests those bypasses.

### 8.3 ALK construction from structures

A scheduled graph workload can combine `RelationshipGraph` for dependencies, `TraversalEngine` for eligible visits, `Budget` for capacity, `Signal` for readiness, `ResourceRegistry` for identities, and `AuditSink` for evidence. The ALK adds mediation, checks that component guarantees meet one another's assumptions, and records ownership for external transitions.

Each structure retains its local contract and claim frame. Composition adds seam obligations rather
than merely unioning child claims. The ALK owns a composed obligation only when its authority covers
all child and seam behavior decisive at the parent frame and the component relies are discharged. A fused "admit, bind
work, reserve capacity, publish ready, and append evidence" transition can issue a stronger
subject-level guarantee than a sequence with interference windows. Where latency or availability
favors separate commits, the architecture records the resulting intermediate states, authority
crossings, and assurance profiles. A domain binding may supply the work performed at the admitted
step; it may not silently introduce a second executor or bypass the composed commit.

### 8.4 Architecture and implementation conformance

ALK conformance requires admission, mediation, ownership, commit, evidence, failure, and execution-authority behavior for a declared subject. The definition permits different crate layouts, runtimes, and products. A structure library supplies components; conformance also requires their governed composition.

A concrete implementation earns only the guarantees carried through a declared abstraction and
refinement from its executable transitions to the applicable formal contracts. Formally verified
components are a necessary construction basis for a formally verified core, but their local proofs
do not by themselves establish composition correctness, total mediation, provider assumptions, or
end-to-end ALK conformance.

---

## 9. Distributed ALK ownership

### 9.1 Collective commit

"The cluster owns the obligation" expands into a protocol statement. A cluster protocol is eligible
to own safety obligation `O` when every transition that can falsify `O` commits through the
declared protocol or is excluded by construction:

$$
Covers_{ClusterProtocol}(O) \iff
\forall t \in ViolatingTransitions(O):
Chosen_{Protocol}(t, Membership, Epoch, CommitRule)
\;\lor\;
Excluded(t)
$$

Lamport's Paxos provides one researched form: a value becomes chosen through intersecting
majorities, with safety derived from the intersection and proposal rules. Other protocols can
instantiate the definition [6]. The EIM frame names the protocol as the canonical owner at the
cluster abstraction; participants may own distinct lower-level obligations in their own frames.

### 9.2 Distributed ownership forms

| Form | Direct owner | Structural basis | Partition consequence |
|---|---|---|---|
| Replicated state machine | The protocol-defined membership acting through its commit rule | Ordered state-machine log with quorum intersection | The protocol preserves its safety rule and may suspend commits when the required set cannot communicate |
| Partitioned authority | Each holder owns a conserved local share; the allocation protocol owns share transfer | `FederatedBudget`, registries, epochs, and non-duplicating transfer | Reachable holders can act within their shares; reassignment waits for the transfer rule |
| Witness federation | The primary authority owns the transition; witnesses own attestations | Audit evidence, signatures, anchors, and consistency comparison | The primary can continue under the stated policy; assurance class and failure ceiling change with witness reachability |
| Delegated external service | The service owns its commit; the ALK owns its request and local response handling | Transport, receipts, reconciliation, replicas, and recovery | Availability and guarantee kind follow the service contract and assurance timing |

Gilbert and Lynch establish the partition constraint for an asynchronous network model [3]:
atomic consistency and total request availability cannot both be guaranteed during a
partition. An ALK cluster therefore states the partition outcome per obligation. Admission
may fail closed, audit creation may require a reachable witness, or a federated budget may
continue within preassigned shares. Each choice produces a different guarantee and failure
cut set.

### 9.3 Cluster TCB

The claim-specific TCB for a collective commit includes the protocol implementation,
membership and epoch authority, quorum or threshold rule, persistent state, key roots,
network assumptions used for liveness, and recovery procedure. A learner's report that a
value was chosen is evidence from the protocol; the safety claim still depends on the
acceptors and their state. The same ownership-assurance distinction applies inside the
cluster.

Reconfiguration deserves its own obligation. Membership changes alter the authority set and
can invalidate quorum intersection, duplicate a partitioned share, or detach old evidence
from the new epoch. An ALK cluster records reconfiguration as a governed transition with an
epoch, commit rule, and evidence record.

---

## 10. Worked example: Kubernetes audit custody

Kubernetes creates audit events inside `kube-apiserver` and can send them to a log file or a
remote webhook backend. The webhook supports asynchronous batch modes and blocking modes;
buffer overflow in batch mode can drop events. This makes the audit path a useful ownership
example because event creation, export, indexing, retention, retrieval, and proof can have
different authorities [16].

Assume an application operator requires evidence of selected Kubernetes API requests and
ships the events to Splunk or an S3 bucket. The EIM record separates the obligations:

| Obligation | Direct owner | Assurance available to the application operator | Guarantee ceiling |
|---|---|---|---|
| Apply the audit policy and create the selected event | `kube-apiserver` audit path | API server metrics, local error records, and request-stage correlation | Follows audit policy coverage and backend mode |
| Export the event | Audit backend and transport path | Blocking acknowledgement, batch counters, retry evidence, and queue monitoring | Batch mode permits a postcommit loss window; blocking modes move processing into the response path, while strict mode can fail a request at `RequestReceived` |
| Accept and index the event | Splunk ingestion/indexing service | Indexer acknowledgement and later search or reconciliation [17] | Receipt semantics determine whether acceptance, indexing, or durable replication was acknowledged |
| Store an immutable object version | S3 service and configured account controls | Successful put response, checksum, version identifier, Object Lock metadata, inventory, and retrieval [18, 19] | Depends on service correctness, credentials, region assumptions, retention mode, and version-specific policy |
| Retain the record for the policy period | External custodian and retention-policy authority | Periodic retrieval, retention-status checks, independent inventory, replica, and external anchor | The custodian owns continuous retention; checks provide sampled detection and replicas provide recovery |
| Prove content and sequence | Evidence producer, key authority, anchor custodian, and verifier | Hash chain, signed receipt, published head, and consistency comparison | Integrity and attribution follow key custody, anchor independence, and evidence availability |

Kubernetes can own event creation, Splunk indexing, and S3 object custody. Queries, retrievals, checksums, Object Lock metadata, and independent anchors provide assurance about the external records. An independent witness changes the evidence dependencies while the service retains control of its storage state.

The claim determines the TCB. "The API request generated a local event before response" has a
different TCB from "the event remains retrievable and immutable for the retention period." A
blocking-strict webhook can make successful audit processing at `RequestReceived` a
precondition for API request progress. The architecture defines what the acknowledgement
means and whether later retention is covered. S3 Object Lock can constrain overwrite and
deletion of a stored object version; the retention claim then depends on S3, the configured
retention mode, versioning, account and key authorities, and the evidence used by the
claimant.

---

## 11. Derived ALK claim views

Three named views group the review questions: audit coverage, policy mediation, and composition.

| View | Required conditions | Review question |
|---|---|---|
| Zero-Gap Auditability | every significant commit is mediated; evidence is created inside the governed commit interval; content, order, custody, retention, and retrieval obligations are explicit | can the claimant connect every covered effect to evidence of the required grade? |
| Unified Policy Enforcement | every covered policy-relevant transition, including workload-level execution control, reaches a governed commit; applicable safety obligations are preserved; environmental and peer relies are discharged | can any covered transition or executor bypass the authority that carries its obligation? |
| High-Integrity Composability | each component establishes its guarantee under its rely; peer guarantees discharge internal relies; shared commits, intermediate states, retries, failures, and delegation seams preserve the composed obligations | does the system guarantee survive at the seams rather than only inside each component? |

For a view `P`, subject `X`, and claimant boundary `B`, keep locally owned claims and
assurance about delegated obligations separate:

$$
Support_B(P,X) = OwnedClaims_B(P,X) \cup ClaimantAssurance_B(P,X)
$$

The record separates `B`'s owner-issued guarantees from its A0-A5 assurance about externally owned obligations. Each entry names the proposition, evidence, assumptions, and failure limits. Composing the entries does not transfer ownership of the external obligations to `B`.

The names are optional summaries of the underlying obligations, authority bindings, and composition arguments.

---

## 12. Formal evidence and claim status

### 12.1 Active structure evidence

Every current catalog structure has specifications, proofs, Verus contracts, correspondence records, cross-checks, and controls. The nineteen primitive and named-composition contracts also have mechanized refinements between executable transition profiles and canonical models. These establish the written formulas and mappings. Section 12.3 separately identifies ALK instantiation evidence.

### 12.2 Placement and composition results

The placement suite checks direct and delegated cases across assurance timing, service failure, and partition. Controls reject postcommit assurance credited as prevention and omitted partition failures. Its parameterized classification proof assumes the placement and controller relationships; it does not establish real authority or separate an external owner's guarantee from a delegator's assurance.

`GuaranteeClaimant` names the recipient, `OwnerOf` supplies action owners, and `PreventionControllers` supplies the set used to calculate a ceiling. `CommitDelegate` is typed but does not enter that calculation. These supplied values leave claimant perspective, controller power, issuance, and assurance class to separate claim bindings.

The claim-relative ownership package defines complete frames, decisive behavior, coverage, canonical ownership, accountability, issuance, assurance, transfer, and TCBs. TLAPS derives consequences of those supplied relations. Controls reject shared owners, non-owner issuance, assurance treated as ownership, and work delegation treated as transfer. Applying the model still requires identifying the system's actual behavior and authority.

The audit-custody instance checks receipt, detection, recovery, and partition ceilings, with a receipt-without-acceptance control. The composition suite proves a parameterized assume-guarantee rule and instantiates it for a finite Budget/audit system. An action-partition proof connects the concrete transition relation to the component relations. No-audit, overspend, omitted-rely, and interference controls test the required conditions.

### 12.3 Evidence map

| Claim surface | Active evidence | Current reading |
|---|---|---|
| Catalog contracts | TLA+ specifications, TLC checks, TLAPS proofs, controls, reductions, and checked registry/generated records | written clauses are formalized; the registry records the discovered schemas, selected modes, clause status, derivation relations, and exact source bindings. This does not make every classification a theorem or instantiate every architectural claim |
| Check-act stability | atomicity bridge, refinement proof, and six paired mechanism-breaking controls | proved under the stated lock and transition assumptions; NoLock is auxiliary because its config changes the state vocabulary |
| Executable correspondence | faithful Verus implementations and action-level ledgers for all current catalog structures; refinement packages for the nineteen primitive and named-composition contracts | mechanized written-profile mappings at the named state/action boundary; they do not resolve the obligation classification |
| Ownership and assurance | claim-relative typed model and proof, discriminating ownership controls, placement model, partition/failure controls, classification proof, and audit-custody instance | the claim-relative consequences and placement classifications hold for supplied relations and modeled cases; these artifacts do not discover real authority or instantiate catalog claim frames |
| Composition | specific catalog theorems; parametric assume-guarantee rule; exact finite-state Budget/audit instantiation and action-partition proof; controls | the generic rule establishes the stated rely/guarantee result; the named machine discharges it exactly, while the result stays scoped to its explicit state, actions, and relies |
| Execution mediation | EIM execution-authority inventory; unmediated-executor definition; ALK model and conditional construction theorem | complete mediation is derived for the represented governed action set when the theorem's exact inventory, path, ownership, catalog sufficiency, and deployment premises hold; no concrete runtime receives that credit here |
| Automation-Layer Kernel | finite semantic model, conditional construction theorem, and four representative profiles | the model selects normalized labels and generic supplied semantics; it does not establish exact catalog predicates, claim-relative authority, or issuer/assurance binding |
| Selected ALK claim boundaries | exact Budget/Sequential predicates and action partition; controller-derived ownership; separate progress, relational, and diagnostic witnesses; shared evidence and assurance interface | actual actions support the complete selected frames under modeled gates, fairness, coupling, clock, and custody premises. The shared interface binds semantic evidence, issuer, claimant, and mechanism claims; no implementation authority follows. See [ALK Claims](alk-claims.md) |
| ALK reference specification | `ALK-SPEC-1` state machine, conformance vectors, proofs, controls, and a static certificate with a read-only claim view | three actual reference-state predicates are bound to complete frames, model-protocol ownership, issuer, recipient, A5 assurance, evidence, and residuals. Legacy ceiling labels remain separate. This does not refine every catalog/profile selection or establish implementation or deployment conformance |

---

## 13. Scope boundary

The evidence establishes the modeled contracts, placement classifications, and claim bindings listed in Section 12. Implementation conformance must connect those results to actual execution and authority. Distributed agreement, correlated Byzantine failures, and product-specific custody need their own models and evidence.

`ALK-SPEC-1` classifies selected credential, database, debug, shared-memory, administrative, recovery, and external-service paths. A runtime claiming complete mediation must also account for its worker pools, asynchronous runtimes, callbacks, devices, helper processes, and external executors, and show how each governed path is mediated or excluded.

---

## References

1. Martin Abadi and Leslie Lamport. [Composing Specifications](https://doi.org/10.1145/151646.151649). *ACM Transactions on Programming Languages and Systems*, 15(1), 1993.
2. James P. Anderson. [Computer Security Technology Planning Study, Volume I](https://csrc.nist.gov/files/pubs/conference/1998/10/08/proceedings-of-the-21st-nissc-1998/final/docs/early-cs-papers/ande72a.pdf). ESD-TR-73-51, 1972.
3. Seth Gilbert and Nancy Lynch. [Brewer's Conjecture and the Feasibility of Consistent, Available, Partition-Tolerant Web Services](https://doi.org/10.1145/564585.564601). *SIGACT News*, 33(2), 2002.
4. Stuart Haber and W. Scott Stornetta. [How to Time-Stamp a Digital Document](https://doi.org/10.1007/BF00196791). *Journal of Cryptology*, 3(2), 1991.
5. Maurice Herlihy and Jeannette Wing. [Linearizability: A Correctness Condition for Concurrent Objects](https://doi.org/10.1145/78969.78972). *ACM Transactions on Programming Languages and Systems*, 12(3), 1990.
6. Leslie Lamport. [Paxos Made Simple](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/paxos-simple-Copy.pdf). *ACM SIGACT News*, 32(4), 2001.
7. Jochen Liedtke. [On Micro-Kernel Construction](https://doi.org/10.1145/224056.224075). *Proceedings of the Symposium on Operating Systems Principles*, 1995.
8. Donn B. Parker. *Fighting Computer Crime: A New Framework for Protecting Information*. Wiley, 1998.
9. Jerome H. Saltzer and Michael D. Schroeder. [The Protection of Information in Computer Systems](https://doi.org/10.1109/PROC.1975.9939). *Proceedings of the IEEE*, 63(9), 1975.
10. Fred B. Schneider. [Enforceable Security Policies](https://www.cs.cornell.edu/fbs/publications/99-1759.pdf). Cornell University Technical Report TR99-1759, 1999.
11. National Institute of Standards and Technology. [Trusted Computing Base](https://csrc.nist.gov/glossary/term/trusted_computing_base). CSRC Glossary.
12. National Institute of Standards and Technology. [Engineering Trustworthy Secure Systems](https://doi.org/10.6028/NIST.SP.800-160v1r1). SP 800-160 Volume 1 Revision 1, 2022.
13. Karen Kent and Murugiah Souppaya. [Guide to Computer Security Log Management](https://doi.org/10.6028/NIST.SP.800-92). NIST SP 800-92, 2006.
14. Ben Laurie et al. [Certificate Transparency Version 2.0](https://www.rfc-editor.org/rfc/rfc9162.html). RFC 9162, 2021.
15. Microsoft. [Getting Started with the Threat Modeling Tool](https://learn.microsoft.com/en-us/azure/security/develop/threat-modeling-tool-getting-started). Microsoft Learn.
16. Kubernetes. [Auditing](https://kubernetes.io/docs/tasks/debug/debug-cluster/audit/). Kubernetes Documentation.
17. Splunk. [HTTP Event Collector Examples](https://docs.splunk.com/Documentation/Splunk/latest/Data/HECExamples). Splunk Documentation.
18. Amazon Web Services. [Locking Objects with S3 Object Lock](https://docs.aws.amazon.com/AmazonS3/latest/userguide/object-lock.html). Amazon S3 Documentation.
19. Amazon Web Services. [Amazon S3 Data Consistency Model](https://docs.aws.amazon.com/AmazonS3/latest/userguide/Welcome.html#ConsistencyModel). Amazon S3 Documentation.
20. Brian Moore. *Automation Structures: A Structural Theory for Automated Systems*. Research manuscript.
21. Brian Moore. *Automation Structures Formal Corpus: Catalog, Specifications, Proofs, Controls, Refinements, and Generated Reports*. Research artifact; locations in the repository index.
