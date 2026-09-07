# Execution Structures

## Four Recurring Base Structures for Executing Automated Work

Related documents: [Automation Structures](automation-structures.md) is the capstone; [Domain Abstraction Collapse](domain-abstraction-collapse.md) is the discovery method; [The Automation-Layer Kernel and the Execution Integrity Model](execution-integrity-model.md) covers ownership and assurance; [formal-methods.md](formal-methods.md) records the active evidence.

---

## Abstract

An execution structure determines how admitted work runs. This paper identifies four recurring forms: sequential, fork-join, step graph, and stream graph. They differ in what can be active together, what enables the next piece of work, and when results become available. They also define the conditions under which work can close. An execution profile records these observable features at a declared boundary, including what counts as progress and which state persists. Those profiles provide a basis for comparing the structures.

Formal models and implementations establish the stated contracts, profile distinctions, refinement relations, and one nested composition. The vocabulary comes from the systems surveyed and can change when a system's behavior requires a different structure or observation model.

The design method separates a request to do work from its admission, execution, and effects. Different segments can use different execution structures, provided their composition preserves the selected obligations. The Execution Integrity Model identifies their owners. Claims about delivery, recovery, ordering, and progress depend on those contracts and runtime assumptions.

---

## 1. The engineering problem

An execution design must explain when work can start and how much may run at once. It must also explain when downstream work sees results. Failure and backpressure add further questions about what state survives and which transitions must wait. The design must identify which authority, if any, controls each transition.

Product labels leave these choices open. "Event-driven" names a trigger; "actor" names an entity and messaging model; "workflow" often describes authoring and durability. An execution profile makes the runtime behavior explicit at a chosen boundary.

The four structures emerged from a survey of automation platforms after product vocabulary was removed. They provide starting choices for discrete execution design, including compositions where different segments need different progress rules.

A separate search screened event-driven, actor, cyclic-workflow, self-modifying, nested-executor, tick-driven, and other model-of-computation candidates for a fifth structure. None met the admission conditions in the search's scope. Tick-driven, unrestricted self-modifying, and adjacent coordination cases remain open; the paper does not rely on this search as proof of completeness.

### 1.1 Theory statement and validation contract

The formal work tests the proposed structures and their relationships. An unfalsifiable property, behavior-erasing refinement, or unstated boundary can require a model correction, revised claim, or new structure.

The validation contract tests four parts of the current account:

| Clause | Question for the formal program |
|---|---|
| Structure fidelity | Can a formal model for each named structure faithfully represent its active-work, dependency, progress, handoff, persistence, and closure semantics? |
| Relational structure | Are the induced profiles observably distinct under an explicit projection, and which refinement relations hold under explicit mappings and assumptions? |
| Composition | Under which seam guarantees do nested and connected execution structures preserve their declared obligations? |
| Validation-set accounting | Which admitted execution segments in the frozen validation set receive a faithful structure recipe and induced profile, and which remain as residuals? |

The frozen validation set covers all four clauses. Each structure has a TLA+ model, TLAPS proofs, a Verus executable, correspondence records, cross-checks, and controls. The set includes one nested composition and one admission segment outside the execution projection. Section 11 records the results and model limits; Section 13 states the refutation conditions.

### 1.2 Evidence labels used in this paper

The paper separates six kinds of statement.

| Label | Meaning |
|---|---|
| `DEFINED` | A term or analysis rule on the current theory surface |
| `DERIVED` | A consequence of Automation Structures boundaries, strata, or obligation method proposed for preservation under the execution-structure account |
| `TLC-CHECKED` | A state-machine statement explored at the named finite bounds |
| `TLAPS-PROVED` | A theorem proved under its stated assumptions |
| `VERUS-VERIFIED` | An executable implementation contract verified by Verus |
| `GUIDANCE` | A builder-facing rule whose value is operational; it is not promoted to a theorem |

Explanatory prose inherits its section's status. Definitions state what is to be tested; proof and checking labels identify the results. Each result applies to its written property and assumptions.

### 1.3 Claim boundary

The four structures are the construction vocabulary induced by the declared scope and
observation model. Structure selection does not determine a product architecture or a cost order.
A profile refinement transfers the behavior stated in its mapping rather than the wider
reliability properties of an implementation. The present scope covers discrete software work
segments, not continuous-time physical processes or synchronous-reactive fixed-point semantics.

A segment that cannot be represented without losing behavior relevant to its obligations is evidence for revising the vocabulary, boundary, or claim.

---

## 2. Where execution structures sit in Automation Structures

### 2.1 Automation begins at the obligation boundary

Automation begins when a system accepts responsibility for work without a human enforcing each step. Examples include capacity limits, authorized effects, dependency ordering, duplicate-effect prevention, and audit records bound to their actions.

Execution profiles expose where responsibilities can fail. A sequential loop can overspend; a join can close with a missing branch; a step graph can release work on stale state; a stream can lose or duplicate records. The selected contracts and enforcement owners determine which outcomes the system excludes.

### 2.2 Execution structure is a construction skeleton across the strata

Automation Structures accounts for a composition with four strata:

| Stratum | Contribution to an execution design |
|---|---|
| Runtime givens | Atomicity, time, thread or process execution, memory ordering, durable storage assumptions |
| Abstraction primitives | Governed state and violable obligations such as budgets, registries, audit chains, convergence rules, and traversal under a cost limit |
| Connective forms | Obligation-free plumbing such as guards, cursors, windows, projections, markers, and joins |
| Domain parameters | The logic, values, scoring rules, operators, effects, and identities supplied by the application domain |

An execution structure combines control state and transition rules across these strata. The same structure can execute different primitives and domain logic, while one primitive can participate in several execution structures. Its profile describes the observable execution behavior.

The builder-facing composition is:

$$
AutomatedExecutor = ExecutionStructure + ObligationStructures + DomainLogic
                    + RuntimeGivens + OwnershipAndAssurance
$$

Execution shape and execution contract are separate parts of the description. Control state defines how work moves; a selected execution contract specifies responsibilities such as ordered advance, predecessor-gated activation, or truthful closure. Additional structures supply capacity, evidence, and other obligations required by the system.

For example, a buffer retains items, a Budget contract enforces a capacity limit, and a stream graph advances records between active operators. A design may need all three.

### 2.3 Request, admission, execution, and effect

The method separates four trace regions.

| Region | Structural question | Typical events |
|---|---|---|
| Request | What condition proposes work to the system? | human action, timer, message, dependency notification, interrupt, pull |
| Admission | What licenses the request to become an execution instance? | authorization, quota check, deduplication, capacity reservation, policy gate |
| Execution | How does accepted work become active, make progress, hand off, and close? | start, branch, node release, record transfer, barrier, completion, cancellation |
| Effect | Which transition changes governed external or durable state, and what evidence binds to it? | write, publish, allocate, send, actuate, commit, audit append |

The request region answers how work is invoked. The execution region answers how work runs. A
timer can propose work that later executes sequentially, fans out, enters a step graph, or feeds a
long-lived stream. A message can do the same. Trigger vocabulary therefore does not by itself
determine an execution structure.

Admission is also separate. A webhook may arrive, fail authorization, and not create an
execution instance. A record may be present on a queue but remain inadmissible because capacity is
reserved elsewhere. Reliable architecture begins by keeping "request observed," "work admitted,"
"work started," and "effect committed" as separate facts.

---

## 3. The unit of analysis

### 3.1 Structure and profile

`DEFINED.` An execution structure is the mechanism a builder implements or configures. It owns the
control state and transition rules by which admitted work becomes active, makes visible progress,
hands results to other work, and reaches a declared outcome.

`DEFINED.` An execution profile is the observation of those mechanics at a declared boundary. It
supports classification, comparison, refinement, and audit. A builder selects an execution
structure. A reviewer derives its profile from the system that was specified or built.

This separation gives the theory two tests. Construction adequacy asks whether the structure gives
the builder the mechanisms required by the workload. Profile fidelity asks whether the claimed
label matches the traces the implementation can produce.

### 3.2 Execution segment

`DEFINED.` An execution segment is a portion of a trace with a declared beginning and end for which the runtime presents one
coherent rule for activation, progress, handoff, and closure. Its boundary is chosen relative to a
claim. A whole process may be one segment for a resource-budget claim and several nested segments
for a dependency-ordering claim.

Each segment has at least the following record:

$$
X = \langle B, W, A, D, P, H, S, C \rangle
$$

where:

| Symbol | Meaning |
|---|---|
| $B$ | Declared segment boundary and execution-instance identity |
| $W$ | Work units visible at that boundary |
| $A$ | Active-work relation over those units |
| $D$ | Dependency relation that constrains activation or handoff |
| $P$ | Progress grain visible to the runtime and its dependents |
| $H$ | Handoff predicate that licenses downstream progress |
| $S$ | State-persistence scope across work events and failures |
| $C$ | Closure condition, including success, failure, and cancellation outcomes |

This record organizes a design or runtime inspection. It is not itself a formal machine model.

### 3.3 Observation model

`DEFINED.` The profile method observes five properties of a built or proposed execution segment:

| Property | What the observer records |
|---|---|
| Active multiplicity | Which work units may be active at the same time |
| Dependency visibility | Which relation controls eligibility or transfer |
| Progress grain | Instruction or step, branch, node completion, or record movement |
| Handoff condition | The event that allows another unit to proceed |
| Persistence scope | How long execution state survives and which event resets it |

The profile is the equivalence class induced by this projection over the surveyed systems.
Two systems may differ in programming language, deployment topology, retry policy,
entity model, or
domain content while producing the same projected execution behavior. They may still differ on
obligations that the projection does not record.

### 3.4 Structure selection and profile assignment depend on the boundary

An Erlang process commonly handles one message sequentially, while a network of such processes may
present queue-mediated record progress at a wider boundary. A workflow task may run a fork-join
computation internally, while the workflow releases its successor only after task completion. A
stream operator may execute a sequential function for each record. None of these descriptions is
inconsistent. Each names a different segment boundary and may require a different contained
structure.

A useful construction statement therefore includes the boundary in the sentence:

> Within boundary $B$, structure $S$ executes the work and induces profile $M$ under observation
> model $O$.

Removing $B$ turns a structural statement into a product label.

---

## 4. Four recurring base execution structures

The first table gives the induced profiles. The second gives the minimum construction skeleton a
builder looks for in the design. A product may combine roles or delegate them; the construction
account records where the relevant mechanisms live.

| Structure and induced profile | Active work | Dependency form | Progress grain | Handoff | Persistence scope |
|---|---|---|---|---|---|
| Sequential | At most one visible unit | Total order | Step completion | Prior step completes | Current invocation or durable cursor |
| Fork-join | A set of sibling branches | Common fork and join epoch | Branch completion | Join predicate holds | Fork epoch through barrier closure |
| Step-based graph | Eligible graph nodes | Predecessor relation | Node completion | Required predecessors complete | Graph run and its durable node history |
| Streaming graph | Operators that remain active across item transfers, plus queued items | Directed queue or channel relation | Record transfer or firing | Input available and downstream capacity or rendezvous holds | Operator state across records, retained according to lifecycle policy |

| Base structure | Minimum construction skeleton |
|---|---|
| Sequential | Execution-instance state, ordered cursor, one logical active locus, step transition, and declared closure |
| Fork-join | Fork epoch, branch-set registry, sibling activation, branch outcomes, join predicate, and result closure |
| Step-based graph | Versioned work graph, node/run registry, eligibility evaluation, node activation, committed completion, and graph closure |
| Streaming graph | Operator and edge state, transfer mechanism, flow control, item position, persistent operator state, and lifecycle boundary |

### 4.1 Sequential

`DEFINED.` The sequential structure presents one active work locus at the selected boundary and a total
order over visible work transitions. The next unit becomes active after the prior unit completes or
yields according to a declared cursor. The structure may run on a preemptive operating system; the
claim concerns logical work at the chosen boundary, not physical possession of a processor.

Typical instances include a command script, a single request handler, one actor message handler,
an imperative transaction body, and the per-record function inside a stream operator. The same
structure also describes a durable interpreter that advances one recorded instruction at a time,
provided its externally visible progress remains totally ordered.

Sequential structure exposes these common seams. The statements are conditional design
requirements for systems that make the corresponding promise:

- Cursor or program-counter correspondence with the effect already committed.

- Retry distinction between work that did not commit and work that committed before acknowledgement.

- Cancellation boundary for the last permitted commit and the disposition of partial local state.

- Audit-order correspondence with effect order when the system claims a truthful trace.

The sequential contract must be combined with any additional guarantees the system requires. A durable cursor may need a `ResourceRegistry`, a resource ceiling a `Budget`, and commit evidence an `AuditSink`.

### 4.2 Fork-join

`DEFINED.` The fork-join structure creates a set of sibling branches from one execution epoch, permits more than
one branch to run, and closes the epoch under a join predicate. The branches have no required
topology among themselves at this structure boundary. If branch B may start only after branch A
finishes, the boundary contains a step graph rather than a pure fork-join structure.

The join predicate need not mean successful completion of the full branch set. Production policies
include full completion, first acceptable result, quorum, threshold, or cancellation after a
winner. Those are domain and governance choices layered on the fork and join mechanics, so the
construction account states the selected rule as part of closure.

Fork-join exposes these common seams under the guarantees a system chooses to make:

- Fan-out identity for the intended branch set and fork epoch.

- Shared-capacity reservation or partitioning across concurrent branches.

- Join-state distinction among completed, failed, cancelled, missing, and superseded branches.

- Result-aggregation order, associativity assumptions, and duplicate policy.

`FederatedBudget` is the natural choice when a master capacity is carved into branch-local shares.
`Reduction` can govern ordered aggregation. `CompetitiveSelection` can govern a winner or ranked
subset. `AuditSink` can bind branch and barrier evidence. These entries are selected only when the
system makes the corresponding promise.

### 4.3 Step-based graph

`DEFINED.` The step-based graph structure represents work as nodes connected by a dependency relation.
A node becomes eligible under a predicate over predecessor state, runs as a unit, and publishes
completion as the event that releases dependent nodes. Completion is the progress grain observed
by the graph runtime.

The graph may be acyclic or cyclic. Cycles require an execution rule that distinguishes iterations,
epochs, or convergence state; drawing an edge back to an earlier node does not supply that rule.
The graph may also be authored as code. Visual declaration is not part of the structure.

Step-based graph structure exposes these common seams under the guarantees a system chooses to
make:

- Correspondence between the dependency view used for release and committed predecessor states.

- Node-run identity across retry, replay, duplicate dispatch, and a new logical run.

- Completion semantics that identify committed effects and any effects permitted to remain pending.

- Graph-version semantics for in-flight runs.

`RelationshipGraph` can govern edge and adjacency agreement. `ResourceRegistry` can own node-run
identity and authoritative status. `Budget` can govern admission and concurrency. `Signal` can
represent pending and delivered release notifications. Cyclic work may require
`ConvergenceGovernor`. Evidence about node and effect closure may require `AuditSink` and
`ActuationPass`.

### 4.4 Streaming graph

`DEFINED.` The streaming graph structure represents operators connected by queues, channels, or
rendezvous edges. Operators process items while upstream operators may remain active.
Progress is observed at record transfer or operator firing rather than at completion of the whole
operator. State commonly persists across records until a lifecycle event resets or restores it.

The construction account includes a flow-control rule wherever a producer can outrun a consumer. A
realization may use queues with capacity limits, demand, credits, rendezvous, rate control, or admission at a
broker. The builder records the actual mechanism and the boundary at which it constrains producers.

Streaming graph structure exposes these common seams under the guarantees a system chooses to
make:

- Queue-admission behavior when capacity is unavailable.

- Loss, duplication, ordering, partitioning, and replay semantics at the consumer's effect boundary.

- Checkpoint and recovery correspondence with input position and committed outputs.

- Iteration, progress, or convergence rules for cycles.

`Budget` or `RateLimit` can govern queue and processing admission. `RelationshipGraph` and
`ResourceRegistry` can govern topology and endpoint identity. `Reduction` can bind consumed-prefix
state to an aggregate. `Signal` can carry delivery bookkeeping. `ConvergenceGovernor` can govern
iterative progress. `AuditSink` can bind transfers, checkpoints, and externally visible effects.

### 4.5 The unit-of-progress distinction

The primary distinction used here for graph execution is the unit visible to downstream work. In a
step-based graph, downstream eligibility depends on predecessor completion. In a streaming graph,
downstream work may consume a record while its upstream operator remains active. This distinction
is structural because it changes which states and interleavings the runtime must represent.

State persistence is a practical field test. If node-local execution state resets when the node
finishes and successors observe a completed node result, the segment is step-based. If operator
state persists across item transfers and successors make progress before the operator closes, the
segment is streaming. Micro-batch systems are classified at the boundary relevant to the
claim: a micro-batch scheduler may be step-based even when its user API consumes an unbounded data
source.

---

## 5. Invocation is separate from execution

### 5.1 Trigger vocabulary

`DEFINED.` Invocation is the relation by which an environmental event proposes work at a boundary.
Common sources include human action, time, message arrival, dependency notification, network
request, hardware event, watchdog expiry, and downstream demand. A source says why a request
exists. It does not say how accepted work progresses.

The same trigger can feed each named structure:

| Trigger | Sequential structure | Fork-join structure | Step-graph structure | Stream-graph structure |
|---|---|---|---|---|
| Timer | Rotate one file | Scan shards in parallel | Start a scheduled workflow | Emit a periodic record into a live topology |
| Message | Handle one command | Query replicas concurrently | Start a durable process | Deliver one item to a long-lived operator |
| Human action | Run one maintenance operation | Launch a parallel test set | Approve a release workflow | Open a live monitoring subscription |
| Dependency notification | Execute one continuation | Release sibling computations | Mark a graph node eligible | Wake an operator with queued input |

Conversely, a step graph may be invoked by a timer, API call, repository event, or a
message. A stream graph may be fed by devices, logs, user-interface events, or internal records.
The method therefore records invocation and execution structure in separate fields of an
architecture description.

### 5.2 External trigger and internal eligibility

An internal handoff can look like a trigger. When node A completes and node B becomes ready, the
completion event invokes B in an informal sense. This paper keeps two levels separate:

- External invocation creates or addresses an execution instance at the segment boundary.

- Internal eligibility is part of the execution structure's handoff rule within that instance.

The distinction matters for identity and deduplication. Repeating an external request may create a
new graph run. Replaying an internal node-release message should usually address the existing run
and existing node attempt. Treating both as generic "events" erases a difference an obligation
depends on.

### 5.3 Admission belongs between trigger and execution

`DERIVED.` An invocation becomes automated work only after the system accepts responsibility for
it. The acceptance transition may need authorization, capacity reservation, policy evaluation,
deduplication, or a durable receipt. This acceptance is a governed commit, distinct from observing
the trigger.

A reliable runtime records at least these identities separately:

| Identity | Meaning |
|---|---|
| Request identity | The environmental proposal, which may be repeated or redelivered |
| Execution identity | The accepted unit of responsibility created by admission |
| Attempt identity | One start or retry of work within the execution |
| Effect identity | The governed external commit used to detect or prevent duplicate effects |

Conflating them produces familiar failures: one redelivered request creates two executions, one
retry commits two payments, one node completion releases a successor twice, or one replayed record
is counted as new input.

---

## 6. Execution structures compose recursively

### 6.1 One product rarely has one execution structure

Large systems should not be assigned a single structure label. A build service may use a step graph
for target dependencies, fork-join for independent compiler actions, sequential execution inside
each compiler invocation, and a streaming graph for live diagnostic events. A data platform may
use a step graph to deploy a stream graph and sequential transactions to checkpoint its state.
The containment seam is executable in this research: the
[nested CI/CD case study](../formal/examples/case-studies/nested-ci-cd-pipeline/README.md) runs a
fork-join test matrix inside a step graph, and the accepted schedule set equals an independent
enumerator's, 270 schedules in both directions.

The decomposition is recursive. A node, branch, or operator may contain a segment with another
structure. The outer structure governs when the contained segment may run and what its closure
means. The inner structure governs how work progresses inside it. Each induces a profile at its own
boundary.

### 6.2 Four composition relations

`DEFINED.` Four relations describe the compositions used here:

| Relation | Meaning | Main seam |
|---|---|---|
| Containment | A work unit in one structure executes an inner structure | Alignment between inner closure and the outer unit's completion contract |
| Sequencing | One structure phase begins after another structure phase closes | Agreement of state and evidence transferred at the phase boundary |
| Mediation | A request, admission gate, or policy service controls entry to a structure | Acceptance and capacity validity at execution start |
| Feedback | Progress or closure in one segment creates work for an earlier or peer segment | Identity, iteration, and convergence controls for recurrence |

Each seam is a rely/guarantee boundary. If an outer step-graph node treats an inner fork-join result
as complete, the outer graph relies on the inner join's closure rule. If a stream checkpoint is
advanced only after a sequential transaction commits, the stream relies on the transaction's
effect identity and durability. A claim of sound composition depends on the supplied guarantee
matching the rely under the stated assumptions.

### 6.3 Refinement keeps the seam

A more general structure may encode the profile of a constrained one. That expressibility result
does not make their operational contracts interchangeable. A stream-graph runtime configured to
emit only on operator completion may represent step-based progress, but it still uses queue,
checkpoint, and recovery machinery whose failure behavior remains part of the design account. A step graph that
represents fork-join with a star topology still needs the correct barrier and branch-set
obligations.

Refinement licenses a behavioral encoding under a mapping. It does not transfer unstated delivery,
durability, cost, security, or recovery guarantees.

### 6.4 Dynamic and self-modifying work

Dynamic topology does not by itself select streaming execution. A step graph may discover new
nodes while preserving node-completion progress. A streaming graph may keep a declared topology
for its lifetime. An actor network may change addresses while each handler remains sequential at
the handler boundary.

A concrete system with topology change is classified at the progress boundary its claim
concerns; a residual in the frozen validation set changes the account.

---

## 7. Reliability is an obligation analysis

### 7.1 Execution contracts and system obligations

`DERIVED.` Reliability claims specify transitions and traces. A workflow label does not establish single execution, unique effects, durable results, or truthful completion. A stream label does not establish delivery, ordering, replay, or checkpoint consistency.

For each claimed responsibility, the builder selects an obligation schema and creates a complete
claim frame compatible with [Claim-Relative Ownership and Assurance](claim-relative-ownership.md)
and the Execution Integrity Model:

$$
F = \langle Subject, Obligation, Mode, Scope, ObservationBoundary,
AuthorityBoundary, Claimant, FailureModel, Abstraction,
LifecyclePhase, PropertyForm \rangle
$$

The selected contract binds the obligation instance to exact clauses and assumptions. The execution
profile helps enumerate decisive actions, omissions, scheduling choices, and trace relations.
Coverage makes a boundary eligible, and the frame selects one canonical owner or records the
obligation as unowned. The owner's guarantee and the claimant's assurance are results of that
placement analysis, not fields inherited from the reusable contract.

### 7.2 Guarantee ledger

`GUIDANCE.` A production execution design should answer the following ledger for each structure
segment. "Not promised" is a valid answer when it is explicit.

| Concern | Builder question |
|---|---|
| Admission | Which transition accepts responsibility for the request, and can concurrent admission exceed capacity? |
| Eligibility | What state licenses work to start, and is that state stable until the start commit? |
| Multiplicity | Are requests, attempts, deliveries, and effects at-most-once, at-least-once, deduplicated, or unconstrained? |
| Ordering | Which order is promised, at what boundary, and which events may be reordered? |
| Resource limits | Which queues, workers, attempts, graph expansions, or iterations have enforceable ceilings? |
| Isolation | Which work unit may read or mutate which state and resource while peers are active? |
| Progress and closure | Under which fairness and availability assumptions is progress expected, and what makes closure truthful? |
| Recovery | Which state is durable, how is it restored, and how are already committed effects reconciled? |
| Cancellation | Which transitions remain permitted after cancellation, and what evidence proves the terminal outcome? |
| Evidence | Which claims can the record support, who owns record creation, and what happens when evidence storage fails? |

Each entry needs a contract: queues can lose messages, checkpoints can disagree with effects, retries can fail indefinitely, and hash chains can omit actions.

### 7.3 Check-act stability at execution-structure seams

For transition-falsifiable safety obligations, Automation Structures's stability rule applies
directly to execution structures. A check licenses a later act when the checked predicate remains
stable under permitted interference until commit. The structures examined here introduce intervals
in which that question is asked:

| Execution structure | Typical check-act interval |
|---|---|
| Sequential | Authorization or capacity checked before a later effect |
| Fork-join | Capacity divided before branches consume or the join closes |
| Step-based graph | Predecessor completion checked before a node starts or commits |
| Streaming graph | Queue capacity, ownership, or input position checked before transfer and effect commit |

The reliable design either fuses the check to the act, partitions the obligation so each concurrent
holder owns a stable share, or states the weaker detection or recovery outcome. The structure tells
the builder where interference can enter. It does not close the interval.

### 7.4 Ownership and delegated execution

Execution frequently crosses component boundaries: scheduler to worker, workflow engine to cloud
service, broker to consumer, control plane to data plane, or application to vendor runtime. The
component that requests an effect does not own the effect's external commit merely because it
records the request.

The Execution Integrity Model distinguishes local enforcement ownership from assurance about an
independently controlled outcome. A precommit receipt can let the local owner guarantee that its
own admission will not proceed without that receipt; the receipt does not make the external fact
true or transfer ownership back to the requester. Later reconciliation can provide point
observation or detection within a stated time. An independent copy can support recovery
within stated time and data-loss limits. The external
owner's prevention guarantee remains assurance from the requester's perspective, with the exact
class, trust roots, and failure ceiling stated.

Execution-structure decomposition therefore ends with a placement question: which component or
protocol covers every behavior decisive for the declared obligation? Delegated work creates a trust
boundary and rely but leaves ownership unchanged while the original owner still covers the outcome.
Complete decisive-authority transfer moves ownership and technical accountability. Partial authority
split without one named protocol leaves the end-to-end obligation unowned. The design records the
canonical owner or gap, the delegator's narrower local guarantees, the assurance profile for the
external outcome, and the failure ceiling.

### 7.5 Safety and liveness remain separate

A runtime may preserve its stated safety invariants while failing to finish useful work. The
execution account therefore states both the safety obligations on each step and the relies under
which progress is expected. Worker availability, scheduler fairness, redelivery within the declared limits, eventual capacity, and
partition healing are environmental assumptions unless a component directly enforces them.

"Some action is enabled" establishes deadlock freedom at a modeled state. It does not establish
that a useful action will eventually occur. Monotone node-state movement does not establish that a
scheduler eventually selects an enabled node. Builder documentation and
formal models should preserve those distinctions.

---

## 8. A builder's method

The procedure produces an execution record: selected structures, observed profiles, composition requirements, and instantiated obligations.

The first construction decision at each boundary is:

| Required work behavior | Base structure to consider first |
|---|---|
| One ordered logical locus | Sequential |
| Sibling units that become active without predecessor relations and resolve at a join | Fork-join |
| Work whose eligibility depends on predecessor completion | Step-based graph |
| Downstream progress while upstream operators remain active | Streaming graph |

### 8.1 Declare the claim and boundary

1. State the user-visible or system-visible claim under analysis. Examples include "an accepted
   deployment either completes or reports a terminal failure," "allocated work stays within the
   tenant ceiling," and "every committed payment has one bound execution record."

2. Draw the authority boundary relevant to that claim. Name external workers, brokers, storage
   systems, policy services, and human approvers that can affect it.

3. Identify the externally visible commit or trace condition that would fulfill or violate the
   claim. Avoid substituting dispatch, acknowledgement, or log arrival for the effect itself.

4. Select an observation boundary fine enough to expose the transitions relevant to the claim. A
   broader product label is insufficient when it hides a nested executor.

### 8.2 Separate request and admission

5. Name the trigger and request identity. Record redelivery, replay, and clock assumptions.

6. Name the admission transition, execution identity, capacity reservation, and rejection outcome.
   If admission is delegated, state the assurance mechanism.

### 8.3 Classify execution

7. Identify active multiplicity, dependency visibility, progress grain, handoff condition, and
   state-persistence scope for the segment.

8. Select the closest named execution structure at that boundary and derive its expected profile.
   Record any behavior the projection erases. Material erased behavior is a residual, not an
   annotation to ignore.

9. Repeat for contained branches, nodes, operators, callbacks, transactions, and recovery paths.
   Record containment, sequencing, mediation, and feedback seams.

10. Define success, failure, cancellation, timeout, and retry as distinct terminal or continuing
    states. Bind them to durable facts where the claim requires durability.

### 8.4 Build the obligation structure

11. Fill the claim ledger. Record the obligation and owner-issued guarantee separately from its
    assumptions, qualifier, evidence, detection or recovery obligations, failure outcome, and any
    `not claimed` disposition.

12. Select the structure and execution contracts whose obligation schemas match the promises. Use
    connective forms for plumbing that defines no independent obligation schema and domain parameters for application logic.

13. For each seam the claim depends on, state the downstream rely and the upstream guarantee. A mismatch is a design
    defect or a reason to narrow the claim.

14. For each obligation, derive the eligible authorities or named protocols from coverage of its
    decisive behavior, then select one canonical owner or record an unowned result. For delegation,
    distinguish delegation of a defined task from authority transfer and record the trust boundary, former and new
    owner where applicable, claimant, exact proposition, assurance classes, remaining local
    guarantees, failure outcome, authority base, and external TCB relies.

### 8.5 Validate the design

15. Construct traces for duplication, reordering, lost acknowledgement, worker crash, stale
    dependency state, queue saturation, cancellation during commit, and evidence-store failure.

16. Check that observability distinguishes request, admission, attempt, effect, and closure. An
    operator should be able to tell which guarantee failed rather than infer it from missing logs.

17. Model the governed state machine when concurrency or failure creates nonlocal
    behavior. Add a discriminating control that breaks the mechanism expected to carry the claim.

18. Re-run the decomposition after implementation. If the built system contains a hidden queue,
    callback, batch boundary, retry loop, or external commit, update the record to match the system
    that will operate.

### 8.6 Selection guidance

`GUIDANCE.` Choose the simplest structure that represents the required progress and failure behavior. Use Sequential for one ordered locus, Fork-join for siblings with a join, StepGraph for completion-gated dependencies, and StreamGraph for progress while upstream operators remain active.

Operational constraints also matter. An existing stream runtime may cost less to operate than a new step engine. The refinement hierarchy compares represented behavior, not product size, cost, or reliability.

---

## 9. Worked structural decomposition

Consider a deployment service used by operators to release an application. The product is often
called a workflow system, but one label hides the execution relevant to its guarantees.

### 9.1 Request and admission

A repository event proposes a release request. The event identifier is the request identity. A
policy gate authenticates the source, checks the target environment, and reserves one deployment
slot under a tenant budget. The durable acceptance record creates the execution identity.

The repository event is invocation. The policy and reservation transition is admission. Neither
determines how the release runs.

### 9.2 Outer step graph

The accepted release enters a graph with build, test, publish, deploy, and verify nodes. Each node
releases its successors only after its declared completion condition holds. At this boundary the
selected structure is step-based graph, and its observable progress induces the corresponding
profile.

The graph needs an authoritative relationship view, node-run identities, a retry rule, a capacity
ceiling, and evidence that node completion corresponds to its promised effect. A `RelationshipGraph`
and `ResourceRegistry` can carry graph and run-state obligations. `Budget` can carry concurrency
admission. `AuditSink` can bind graph transitions to evidence. A node that performs an external
cloud deployment delegates the effect commit and needs assurance appropriate to the release claim.

### 9.3 Inner fork-join test segment

The test node creates sibling shard branches and waits for its declared join policy. At this
boundary the selected structure is fork-join. The outer graph may mark the node complete only when the inner
join produces the guarantee the node contract promises.

A test timeout does not establish branch cancellation. A green result from a quorum join does not
mean every branch passed. A retry must state whether it reuses the fork epoch or creates a new one.
These meanings belong in the join contract.

### 9.4 Sequential effects and streamed observation

Each test shard executes its test list sequentially at the shard boundary. The deployment node may
commit environment changes through ordered sequential transactions. Meanwhile, diagnostic events
flow through a long-lived streaming graph to dashboards and alerting.

Diagnostic events support a claim about deployment effects only when record creation is bound to those commits and the custody assumptions hold. This service uses all four execution structures at different boundaries; its guarantees depend on the contracts and owners at their interfaces.

### 9.5 Resulting execution dossier

| Segment | Trigger or handoff | Execution structure | Principal obligations | Commit owner |
|---|---|---|---|---|
| Release admission | Repository event | Outside profile; governed admission | identity, authorization, tenant capacity, durable acceptance | Deployment control plane |
| Release graph | Admission record | Step-based graph | dependency release, run identity, retry, truthful node closure | Workflow scheduler for graph progress; named external services for their effect commits |
| Test shards | Test-node start | Fork-join | branch set, capacity partition, cancellation, join truth | Test coordinator and workers |
| Shard body | Branch start | Sequential | ordered cursor, effect identity, timeout outcome | Shard worker |
| Diagnostics | Governed transition event | Streaming graph | admission within declared limits, ordering scope, loss policy, custody | Telemetry pipeline; effect evidence depends on source placement |

The record supports design and incident analysis. If the release reports success while a target
environment remains unchanged, the team can inspect the external effect assurance and node-closure
contract instead of treating "the workflow failed" as a sufficient diagnosis.

---

## 10. When structural decomposition is adequate

### 10.1 Adequacy is relative to a claim

`DEFINED.` A decomposition is structurally adequate for a declared claim when it meets four
conditions:

| Condition | Test |
|---|---|
| Trace coverage | The transitions the claim depends on appear in a segment or seam |
| Obligation coverage | Promised properties have a named structure, assumptions, commit condition, and failure ceiling |
| Ownership coverage | Each obligation's decisive behavior has a claim-relative enforcement owner or an explicit unowned gap; every trust-boundary crossing has a claimant and assurance profile |
| Seam closure | Recorded consumer relies are met by producer guarantees under stated interference and failure assumptions |

These conditions specify what a decomposition must account for before it supports the declared claim.

### 10.2 Residuals are findings

A residual is behavior that affects the claim but resists faithful representation by the selected
execution structures, their induced profiles, or composition seams. Examples include an opaque vendor commit with no
observable completion fact, a continuous-time control loop outside the discrete-event model, a
human judgment whose decision rule is intentionally unspecified, or a runtime whose progress
semantics change in a way the selected profile record fails to express.

Record the behavior and what it requires: a revised claim or boundary, an assurance dependency, a new execution structure, or a domain-specific model. The decomposition must preserve the behavior that affects the claim.

### 10.3 The practical answer to "how far can this system be decomposed?"

The method supports recursive decomposition of discrete work at a chosen observation boundary. It
can expose nested executors, trigger and admission paths, governed commits, and trust
boundaries until the record is adequate under the declared claim and the criteria above.

Stop when the four adequacy conditions hold for the claim. Retain unresolved behavior and the reason it could not be represented.

---

## 11. Formal validation and current evidence

### 11.1 Validation questions and dispositions

The validation results are:

| Research target | Evidence disposition |
|---|---|
| Model fidelity | The four formal models expose active work, dependency, progress, handoff, persistence, and closure; their representation ceilings are retained explicitly |
| Observation model | The paper's profile projection and the mapped formal observations are stated; omitted product semantics do not transfer through refinement |
| Distinctness | Four finite witnesses reproduce twice cold with the expected counterexamples |
| Refinement | Four executable-to-model and three model-to-model relations are mechanized; direction and loss boundaries remain explicit |
| Composition | The frozen validation includes fork-join inside a step graph, with the inner join guarantee discharging the outer node-closure rely |
| Invocation boundary | Deployment admission is preserved as an out-of-projection residual rather than mislabeled as execution |
| Obligation connection | The validation rows identify admission, effect, custody, retry, and closure obligations while execution shape remains separate from the obligations in each selected execution contract |
| Validation-set test | Eight frozen segments receive seven faithful structure recipes or compositions and one explicit admission residual |

The formal chains answer structure-specific questions without erasing their ceilings.
Sequential represents one active logical locus and ordered effect progress. Fork-join carries an
epoch, branch-set identity, and falsifiable join rule without treating omitted sibling
communication as a proved absence property. Step-based graph preserves predecessor gating and
truthful monotone completion while leaving scheduler fairness and cyclic progress outside its
safety model. The StreamGraph evidence establishes FIFO flow within each queue's capacity and conservation for its exact
three- and four-node linear chains. Current-tree supplemental evidence also establishes per-branch
and copy conservation plus fairness-conditioned drain for one finite one-source/two-sink profile.
The preserved fan-out counterexample still shows why the old scalar conservation invariant cannot
be generalized across topology changes.

The results apply to the frozen set and its observation model. Another projection may merge distinctions, and another system may require a new structure.

### 11.2 Formal chains

`TLC-CHECKED`, `TLAPS-PROVED`, and `VERUS-VERIFIED.` The accompanying artifact contains the four
canonical TLA+ models (the artifact tree names them carriers), checked TLAPS preservation proofs,
faithful Verus executables, action-level correspondence records, focused known-answer tests, and
controls for the distinct implementation seams. It also contains the refinement models and
distinctness witnesses under the observation model. [formal-methods.md](formal-methods.md)
identifies the exact selectors and claim ceilings.

The models represent these cores:

| Structure model | Modeled state | Principal checked behavior |
|---|---|---|
| Sequential | Program counter, value, active flag, history | Ordered advance with one modeled active locus |
| Fork-join | Worker states, phase, output readiness and snapshot | Independent branch progress followed by barrier and output closure |
| Step-based graph | Node state over a supplied edge relation | Predecessor-gated activation and monotone node-state progress |
| Streaming graph | Per-edge queues, ingested and emitted counters | Queue capacity enforcement and record conservation under the stated topology restriction |

`StreamGraphFanout_NEG` shows why scalar record conservation fails on fan-out: one ingest creates copies in two queues while `LinearGraphAssumption` still holds. The supplemental `StreamGraphFanout` model counts each branch and total copies, requires capacity in both queues, and proves drain under weak fairness. Its TLC run reaches 35 states; drop-branch and no-fairness controls detect the intended failures; TLAPS proves 493 obligations. The separate `FiniteTopologyStreamGraph` contract addresses admitted finite topologies; see [formal-methods.md](formal-methods.md).

### 11.3 Current refinement evidence

`TLC-CHECKED` and `TLAPS-PROVED.` The core hierarchy is represented by these mappings:

$$
Sequential \sqsubseteq StepGraph
$$

$$
ForkJoin \sqsubseteq StepGraph
$$

$$
StepGraph \sqsubseteq StreamGraph
$$

Each statement is scoped to its model, mapping, parameters, and observation. The
direction says that the constrained machine's modeled behavior can be represented by the target
machine under the mapping. It does not say the implementations are interchangeable.

Actor identity, addressing, supervision, and message invocation remain orthogonal concerns. A
handler or wider actor network receives an execution profile only after its boundary and progress
grain are chosen; no actor-specific refinement is needed for that analytical point.

### 11.4 Current distinctness witnesses

`TLC-CHECKED.` The current witnesses distinguish observable behaviors used by the profile account:

- Sequential does not represent two concurrently running fork branches at its modeled boundary.

- Fork-join does not represent topology-induced predecessor release among sibling branches.

- Fork-join does not represent downstream record progress before the fork epoch reaches its
  barrier.

- Step-based graph does not represent downstream record consumption before upstream node
  completion.

The witnesses establish asymmetry for the encoded machines. They do not prove that no alternate
taxonomy can describe the same behaviors.

### 11.5 Retained representation ceilings

The models have the following representation limits:

- Some sequential properties are enforced by representation and are not falsifiable inside the
  model. They are structural ceilings, not discriminating invariant checks.

- Fork-join's lack of inter-worker communication is also a representation ceiling in the current
  model. The theory requires only that siblings have no profile-defining predecessor topology;
  shared state or communication is a separate interference question. The account therefore makes
  no defining fork-join claim from that modeled absence.

- The step-graph model advances node state monotonically after predecessor completion. It does
  not represent explicit iteration, seed, or convergence rules for cyclic work.

- Streaming record conservation is restricted to the graph shape stated by the model. Fan-out
  changes the accounting multiplicity and needs a generalized invariant rather than a claim that
  broadcast is invalid.

- The streaming model's named liveness predicate is a state-level enabled-action condition. It
  supports deadlock-freedom reasoning at the modeled states, not eventual useful progress.

A property may hold because all reachable states satisfy it, because the model excludes a violating behavior, or because an assumption restricts the cases considered. The evidence distinguishes these reasons.

## 12. Relationship to prior work

The following work addresses related execution and composition questions.

| Prior work | Question it answers | Relationship to this paper |
|---|---|---|
| Lee and Sangiovanni-Vincentelli's tagged-signal framework | How can models of computation be compared through tag systems and composition? | Their denotational dimensions retain timing and causality distinctions that the profile projection omits |
| Mokhov, Mitchell, and Peyton Jones's build-system factoring | How do schedulers and rebuilders compose within build systems? | Their scheduler and rebuilder space refines design choices inside work commonly represented here as step-based graph execution |
| Naiad and timely dataflow | How can batch, streaming, and iteration share a progress-tracking substrate? | Pointstamps and frontiers provide within-profile progress semantics beyond this paper's profile label |
| Akidau and colleagues' dataflow model | How should finite datasets and continuous data streams be windowed, triggered, and accumulated? | Their what/where/when/how factoring addresses correctness inside data processing rather than the execution projection alone |
| Russell, van der Aalst, and ter Hofstede's workflow patterns | Which control-flow patterns recur in workflow systems? | Their pattern catalog distinguishes many dependency and join policies inside step-based execution |
| Burckhardt and colleagues' durable functions | Which semantic primitives support stateful serverless work? | Workflows, entities, and critical sections cross execution, entity, and coordination concerns that this paper keeps separate |
| Fowler, Lindley, and Wadler's actor/channel translations | Under which encodings can actor and channel calculi preserve type and semantics? | Their result relates entity and communication representations; it does not by itself determine a handler boundary's profile |
| Mattson, Sanders, and Massingill's parallel patterns | Which recurring patterns organize parallel programs? | Their algorithm and coordination patterns operate at finer and wider levels than the profile projection |

The profile groups systems by active work and visible progress. It omits distinctions in time, determinism, windowing, recovery, authoring, scheduling, and communication. Designs that depend on those distinctions need the corresponding domain models.

---

## 13. Refutation Conditions and Claim Boundary

The execution-structure account is revised when evidence crosses one of these boundaries.

| Current statement | Refuted or narrowed by |
|---|---|
| The named structures induce distinct profiles under the stated observation model | A distinctness witness that no longer violates, or a mutual refinement that erases the asserted asymmetry |
| The tested hierarchy relates the encoded structures | A failed refinement proof or a mapping that requires behavior an obligation depends on that the target excludes |
| The structure and profile projection are useful for the stated scope | A system in scope whose execution behavior resists faithful representation and isolation as a composition seam |
| The builder method provides claim-relative structural accounting | A system claim for which trace, obligation, ownership, and seam coverage all pass while an unrepresented transition can still violate the claim |

A proposed fifth structure is evaluated against the candidate-qualification criteria. No theorem establishes that these four structures are complete. Such a theorem would require a complete formalization of the admissible simulation class.

The eight-segment validation record applies the projection to deployment and LeanFormer
segments, preserves admission as a residual, exercises all four structures, and checks one nested
fork-join/step-graph seam. Additional examples receive evidence credit only when their scope and
claim are registered; broad framework reproduction alone receives none.

Continuous-time execution, synchronous-reactive fixed points, changing observation boundaries, and
other progress models are outside the current claim.

---

## References

- Akidau, T., et al. (2015). The Dataflow Model: A Practical Approach to Balancing Correctness,
  Latency, and Cost in Massive-Scale, Unbounded, Out-of-Order Data Processing. *VLDB*.
- Burckhardt, S., et al. (2021). Durable Functions: Semantics for Stateful Serverless. *PACMPL / OOPSLA*.
- Fowler, S., Lindley, S., and Wadler, P. (2017). Mixing Metaphors: Actors as Channels and Channels
  as Actors. *ECOOP*.
- Lee, E. A., and Sangiovanni-Vincentelli, A. (1998). A Framework for Comparing Models of
  Computation. *IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems*,
  17(12).
- Mattson, T. G., Sanders, B. A., and Massingill, B. L. (2004). *Patterns for Parallel
  Programming*. Addison-Wesley.
- Mokhov, A., Mitchell, N., and Peyton Jones, S. (2018). Build Systems a la Carte. *PACMPL / ICFP*.
- Murray, D. G., McSherry, F., et al. (2013). Naiad: A Timely Dataflow System. *SOSP*.
- Russell, N., van der Aalst, W. M. P., and ter Hofstede, A. H. M. (2016). *Workflow Patterns: The
  Definitive Guide*. MIT Press.
