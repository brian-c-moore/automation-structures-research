# State-Based Replicated JSON Object

Artifact ID: `FEX-DOM-DIST-01`

This case study reconstructs a finite state-based replicated JSON-object subset from retained
Automation Structures parts. It covers disconnected scalar assignments and deletes, concurrent
values, stale and duplicate state delivery, reordered delivery, causal overwrite, observed
deletion, and convergence after complete delivery.

The result is an existing-structure composition. No new primitive, connective form, execution
structure, or named composition was needed.

## Claim

For the registered finite JSON-object subset and delivery schedules, the shared-structure
construction preserves the state-based merge premises, agrees with separate issued-operation and
exact-union references, and converges after complete delivery, while the mechanized premise-binding
model passes its positive and isolated-control checks.

The evidence addresses different questions:

| Question | Evidence |
|---|---|
| Under which algebraic and delivery premises do state-based replicas converge? | The cited CRDT literature |
| Does this construction bind its real identities, merge inputs, merge result, effect target, and complete-delivery verdict to those premises? | The executable recipe, formal model, and premise controls |
| Does the JSON view computed after the merge preserve causal overwrite, concurrent values, and deletion for the declared subset? | A structure-free issued-operation evaluator and the JSON behavior witnesses |

## Source territory

The source model uses a finite stable replica set. Each local edit receives a unique
`(replica, counter)` operation identity and records every operation identity visible at its source.
A replica payload is a grow-only set of those operations. State merge is exact set union. A path
query returns the causally maximal assignments at that path; a maximal delete contributes no value.

The source authorities are:

- [Shapiro, Preguica, Baquero, and Zawirski, 2011](https://doi.org/10.1007/978-3-642-24550-3_29),
  for strong eventual consistency and the monotonic semilattice route for state-based CRDTs;
  [Shapiro et al., INRIA RR-7506](https://inria.hal.science/inria-00555588), for add-only sets
  ordered by inclusion, union as least upper bound, and uniquely identified replicated events.
- [Kleppmann and Beresford, 2017](https://doi.org/10.1109/TPDS.2017.2697382), for the source behavior
  of a replicated JSON map with offline edits, delayed or reordered delivery, concurrent values,
  deletion, and convergence.

This artifact does not copy the Kleppmann-Beresford algorithm. It instantiates the state-based
semilattice route from Shapiro et al. for one declared JSON-object subset and checks its view
behavior separately.

## Exact object model

The document is one root JSON object. A path is a nonempty sequence of string map keys. Each path
has a multi-value register whose scalar values may be null, Boolean, signed integer, or string.

Each replica may perform two local actions while disconnected:

1. Assign one scalar value to a path.
2. Delete the scalar register at a path.

An operation contains its identity, path, action, and the complete set of operation identities
visible at its source. An operation dominates an earlier operation at the same path only when its
dependency set contains the earlier identity. Concurrent assignments are therefore both maximal
and remain visible. A delete hides assignments it observed but does not hide a concurrent
assignment.

Arrays, collaborative text, counters, subtree moves, schema behavior, garbage collection, state
compaction, network protocols, durable storage, and membership change are outside the model.

## Domain-neutral decomposition

| Neutral role | Replicated-object binding | Preserved relation |
|---|---|---|
| Identity | Replica and operation identity | Distinct source events retain distinct governed identities |
| Local authority | One replica payload | Each participant changes only its named local state |
| Monotone state | Grow-only operation set | Every local update and merge moves upward under inclusion |
| Combine | Set union | The committed result is the exact least upper bound of both inputs |
| Effect target | Delivery target replica | A merge changes exactly the named local state |
| Causal marker | Source-visible operation set | A later event dominates only events observed at its source |
| Conflict set | Causally maximal assignments | Concurrent values remain visible without one global winner |
| Execution order | One finite interleaving | Every edit and delivery has one begin and completion record |
| Observation | Complete-state and equal-view verdict | Complete delivery is checked before agreement is accepted |

The stripped process is:

1. Register every replica identity.
2. Begin one local edit and capture that replica's visible operation identities.
3. Register the fresh operation identity and apply the operation to the named replica.
4. Capture a replica payload under a unique message identity.
5. Begin one delivery to a named target.
6. Fold the exact target and captured payloads through the registered join.
7. Apply the committed merge result to the named target and complete the delivery.
8. Check the join premises on the actual construction operator.
9. Require every correct replica to contain every issued operation.
10. Compare each materialized view with the separate issued-operation evaluator.

## Construction from retained parts

| Retained part | Work performed in this case |
|---|---|
| `ResourceRegistry` | Registers replica, operation, and captured-state identities without replacement |
| `Reduction` | Folds the exact target and delivered payloads through the union function and commits the result |
| `ActuationPass` | Binds a local edit or merge effect to its named replica target |
| `Sequential` | Records one finite edit, capture, or delivery step with begin-before-complete order |
| Typed trace and recipe verifier | Checks unique events and every registered edge for every individual step |

The domain module supplies the content consumed by those parts:

- JSON path and scalar representation.
- Operation construction from one local edit and its source-visible dependencies.
- Set union as the selected state join.
- Causal domination and view materialization.
- Finite script storage and deterministic observation order.

Those functions do not own identity registration, fold commitment, effect-target identity, or
ordered step completion. Their semantic premises remain explicit and executable.

`PropagationPass` is absent because arbitrary state delivery has no common round snapshot or
obligation to finish within an iteration limit. `ConvergenceGovernor` is absent because the target relies on eventual
delivery and observes equality; it does not claim to create delivery or govern fixed-point
detection. `AuditSink` is absent because one predecessor chain would impose a false global order on
concurrent source events.

## Execution structure and causal order

The runner is a single process and `Sequential` records one concrete interleaving. That is
execution scaffolding, not the causal-order mechanism.

Causality is data in each operation's dependency set. Two replicas that edit offline from a common
ancestor produce incomparable operations even though the test runner must call one edit function
before the other. Query dominance is computed by dependency containment and never by runner
position.

The three-replica test delivers the same captured payloads in all six orders and repeats one
delivery. Every order reaches the same payload and view. The multi-input test also passes two- and
three-payload permutations through one shared `Reduction` fold. Together these controls show that
the ordered execution structure records execution without supplying the commutativity or causality on which
convergence depends.

## Join and query verification

For every delivery, the verifier checks:

- The delivered payload is the exact payload registered under the message identity.
- The merge result contains both inputs and equals independently reconstructed set union.
- The shared `Reduction` path was used.
- The `ActuationPass` effect names the declared target.
- The individual begin, reduction, effect, and completion events occur once and in order.

The verifier collects states reached by edits and deliveries and applies the construction's own
merge operator to a finite state family. For the registered three-operation family it checks:

| Law | Evaluations |
|---|---|
| Idempotence | 8 cases |
| Commutativity | 64 pairs |
| Associativity | 512 triples |

These are 584 law evaluations over one exhaustively enumerated eight-state power set, not 584
independent samples.

Before accepting convergence, the verifier independently reconstructs the complete issued state.
Every replica must equal that state. This prevents the degenerate result in which all replicas agree
after all of them lose the same operation.

## Independent executable references

The [reference module](../../rust/crates/formal-example-domains/src/crdt_reference.rs) imports no
shared structures and calls no construction helper.

- `evaluate_issued_operations` derives causally maximal path operations directly from the
  issued-operation registry. It never reads a merged replica payload.
- `reconstruct_lub_union` builds the exact union of two payloads without calling the construction's
  join function or `Reduction`.

The reference shares the operation data types and recorded dependency relation with the
construction. It can detect a merge, materialization, targeting, or completeness error. It cannot
detect a source operation whose causal dependencies were already recorded incorrectly without a
behavioral witness, so overwrite and concurrent-value controls remain load-bearing.

## Formal premise-binding model

The [TLA+ model](formal/CrdtPremiseBinding.tla) strips the process to two replicas, two locally
issued operations, a two-step delivery loop, a join transition, a target effect, and a terminal
convergence gate.

| Invariant | Construction premise |
|---|---|
| `IdentityContentConsistency` | One operation identity does not resolve to conflicting content |
| `ExactJoinBinding` | The exercised join equals exact set union |
| `JoinLawBinding` | The exercised join is inflationary, idempotent, commutative, and associative |
| `ReductionBinding` | A delivery commits the registered join of the exact before-state and payload |
| `TargetBinding` | Only the named target receives the committed result |
| `CompleteDelivery` | A terminal verdict requires every replica to contain every issued operation |
| `StrongConvergence` | Terminal replicas contain equal payloads |
| `SequentialOrder` | Begin, reduction, effect, and completion counters retain their order |

The positive configuration explored 27 generated and 27 distinct states with all declared
invariants green. Six isolated controls produced their required target violations:

| Control | Target | Generated / distinct states |
|---|---|---:|
| Register conflicting content under one identity | `IdentityContentConsistency` | 2 / 2 |
| Use a left-biased combine function | `JoinLawBinding` | 4 / 4 |
| Drop one remote operation from the join | `ExactJoinBinding` | 4 / 4 |
| Apply the result to another replica | `TargetBinding` | 6 / 6 |
| Accept convergence before complete delivery | `CompleteDelivery` | 4 / 4 |
| Complete a delivery before its effect | `SequentialOrder` | 7 / 7 |

The terminal transition already requires equal complete replica states. `StrongConvergence`
therefore checks that terminal equality remains true, but is not an independent convergence
theorem; exact join, complete delivery, executable schedules, and the cited source result carry the
claim at their respective boundaries.

This model check explores the configured finite state space. It does not prove eventual delivery, provide a Rust-to-TLA
refinement theorem, or re-prove the published general convergence result. JSON causal
materialization remains in the executable construction and separate reference rather than this
two-operation structural model.

## Executable results

| Evidence | Result |
|---|---|
| Concurrent assignments | Both replicas retain both concurrent scalar values |
| Offline different paths | Both paths survive and replicas converge |
| Observed overwrite | The later observed assignment hides the earlier assignment |
| Observed delete plus stale delivery | The deleted value does not resurrect |
| Concurrent delete and assignment | The concurrent assignment remains visible |
| Generated value pairs | 64 of 64 matched the separate evaluator |
| Generated path/edit/delivery cases | 8 of 8 matched the separate evaluator |
| Three-replica schedules | All 6 delivery permutations plus duplicate delivery converged |
| Merge-law state family | 8 + 64 + 512 checks passed |
| Executable controls | 10 of 10 were rejected as intended |
| CRDT module tests | 13 passed, 0 failed |
| Formal positive model | 27 generated states, 27 distinct states, all declared invariants passed |
| Formal controls | 6 of 6 produced their required target violation |

The default runner case issues three operations. Both replicas finish with all three operations and
the visible conflict set `{B, C}` at `key`.

## Discriminating executable controls

| Fault | Why final agreement is insufficient | Required observation |
|---|---|---|
| Reuse operation identity | Equal replicas can contain ambiguous content | Registration and content identity reject the run |
| Bypass `Reduction` | A copied payload can converge on a favorable schedule | Per-delivery recipe and inflation checks reject the bypass |
| Left-biased merge | Selected schedules can converge after losing remote state | Join laws, exact union, and completeness fail |
| Treat duplicate as fresh | Replicas can agree after inventing new identities | Idempotence and issued-state equality fail |
| Drop causal context | Replica payloads can be equal while overwrite semantics are wrong | Separate issued-operation evaluator rejects the view |
| Lose concurrent value | Both replicas can agree on the same single winner | Separate evaluator requires every causal maximum |
| Drop delete | Replicas can agree after a deleted value resurrects | Delete witness and separate evaluator reject the view |
| Misdirect delivery | A later delivery can mask an earlier wrong target | Target-bound actuation and per-delivery evidence fail |
| Incomplete convergence | Every replica can agree on the same incomplete state | Complete issued-state equality fails |
| Misorder a later delivery | One correct early edge can hide a later failure | Per-delivery recipe verification rejects the later instance |

The two explicit "agreement remains green" tests are important. One removes a concurrent value from
both replicas; the other removes an issued operation from both replicas. In both cases replica
agreement is true and the complete verifier rejects the run. Agreement is an outcome, not a
substitute for the source premises.

## Run the case

From `formal/examples/rust`, inspect and run the default case:

```powershell
cargo run -p formal-example-runner --offline -- describe FEX-DOM-DIST-01
cargo run -p formal-example-runner --offline -- run FEX-DOM-DIST-01
```

Run another positive scenario and representative controls:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-DOM-DIST-01 `
  --scenario observed-delete

cargo run -p formal-example-runner --offline -- run FEX-DOM-DIST-01 `
  --control lose-concurrent-value

cargo run -p formal-example-runner --offline -- run FEX-DOM-DIST-01 `
  --control incomplete-convergence
```

Positive scenario names are `concurrent-assignment`, `offline-paths`, `observed-overwrite`,
`observed-delete`, and `concurrent-delete-assign`.

Control names are `reuse-operation-identity`, `bypass-reduction`, `left-biased-merge`,
`duplicate-as-fresh`, `drop-causal-context`, `lose-concurrent-value`, `drop-delete`,
`misdirect-delivery`, `incomplete-convergence`, and `misorder-later-delivery`. A control command
succeeds only when construction or verification rejects the mutation.

Run the CRDT tests:

```powershell
cargo test -p formal-example-domains --offline crdt::tests
```

From the `automation-structures` directory, run the model and all isolated controls through the
pinned verifier container:

```powershell
docker build --pull=false --tag automation-structures-proofs verification

docker run --rm --init --network none --read-only --cap-drop ALL `
  --security-opt no-new-privileges --cpus 2 --memory 4g --memory-swap 4g `
  --pids-limit 512 --volume "${PWD}:/source/automation-structure-research:ro" `
  --tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777 `
  automation-structures-proofs run --subject CrdtPremiseBinding --workers 1
```

Add `--format json` to a runner command for the complete public evidence record and summarized run
data.

## Interpretation

This case reconstructs a multi-owner convergence process from retained identity, reduction,
targeted-effect, and execution-order structures. The load-bearing algebra remains domain content,
but it is not hidden: the actual join inputs and commit are bound to `Reduction`, the law checks use
that same construction operator, and the complete-state verifier prevents outcome-only credit.

The case also demonstrates a boundary between execution structure and source semantics. An ordered
runner is compatible with concurrent source events because causal order is represented explicitly
and the combine function is tested under every registered delivery and fold permutation. The
execution structure records what the computer executed; it does not manufacture the partial order
or the join law.

No missing structural shape was found. A general semilattice theorem package could reduce repeated
evidence work in future cases, but one successful use does not justify a new catalog entry and the
published theorem already supplies the implication required here.

## Claim limits and falsifiers

The executable evidence covers the named scripts, generated cases, and one eight-state law
family. The TLA+ result covers two replicas, two operations, and two delivery steps. The case
makes no claim about full replicated JSON behavior, network liveness, failure recovery, storage,
security, production readiness, or performance relative to specialized CRDT implementations.

The result turns red if any of the following occurs:

- A complete registered replica differs from the separately reconstructed issued-operation state.
- A materialized view differs from the separate causal-maximality evaluator.
- Any registered merge-law evaluation fails.
- Agreement is accepted while an issued operation or correct replica is omitted.
- A named construction control passes the complete verifier.
- The formal positive model fails a declared invariant or a paired control misses its target.
- A source-required governed state or commit cannot be placed without inventing unclassified
  behavior.
