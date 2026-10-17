# Nested CI/CD Pipeline

Artifact IDs: `FEX-DOM-CICD-01`, `FEX-DOM-CICD-03`, and `FEX-ASM-06`

This case reconstructs one successful four-job CI workflow from retained Automation Structures
parts. The outer job dependency relation runs through `StepGraph`. The test job opens a nested
two-worker `ForkJoin` epoch, and that outer job cannot complete until the inner carrier crosses its
barrier and publishes the joined result.

The result is a catalog composition. No new primitive, connective form, execution structure, or
named composition was required.

## Claims

The three IDs expose different claim surfaces over the same running construction:

| Artifact | Claim surface |
|---|---|
| `FEX-DOM-CICD-01` | The declared job DAG is bound to `RelationshipGraph`, `TraversalEngine`, and the authoritative `StepGraph` edge and state set |
| `FEX-DOM-CICD-03` | Both registered test partitions complete through `ForkJoin`, receive their declared debits, and appear in the joined result |
| `FEX-ASM-06` | The outer graph and inner worker epoch cross their identity, dependency, capacity, effect, and carrier-handoff seams in one execution |

For the registered finite workflow, the accepted event-schedule set from the shared carriers equals
the schedule set produced by a separate plain-state enumerator. Every accepted construction
schedule produces the six registered outputs.

## Source territory

The source behavior comes from two GitHub Actions documentation contracts:

- [Using jobs in a workflow](https://docs.github.com/en/actions/how-tos/write-workflows/choose-what-workflows-do/use-jobs)
  defines unique job identities, dependency release through `needs`, parallel jobs, and matrix
  expansion.
- [Workflow syntax](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax)
  states that jobs run in parallel by default unless dependencies constrain them, and documents
  `jobs.<job_id>.needs` and matrix jobs.

GitHub Actions is a source illustration. The construction does not call GitHub, parse workflow
YAML, or claim product conformance.

The frozen workflow is:

```text
compile -> static-analysis ---\
    |                          -> package
    +-> test-matrix ----------/
          |-- test-linux
          +-- test-windows
```

The four outer edges are `compile -> static-analysis`, `compile -> test-matrix`,
`static-analysis -> package`, and `test-matrix -> package`. The compute declaration charges two
units for compilation and one unit each for static analysis, both test workers, and packaging.

Only successful execution is in scope. Conditional jobs, failures, retries, cancellation,
timeouts, runner provisioning, caching, secrets, and deployment behavior remain outside the
source model.

## Domain-neutral decomposition

Removing CI/CD nouns leaves these roles:

| Neutral role | Workflow binding | Preserved relation |
|---|---|---|
| Identity | Job and partition IDs | Only registered identities can own governed work or output |
| Dependency | `needs` edges | An item becomes eligible only after every predecessor completes |
| Frontier | Jobs reachable from the root | Every declared item is visited once |
| Worker set | Linux and Windows test partitions | The joined result covers every declared sibling |
| Barrier | Test aggregation point | Publication follows full worker completion |
| Capacity | Six compute units | Charged work cannot exceed the declared total |
| Effect | Named artifact or test result | A completion applies to its allocated output identity |

The stripped process is:

1. Commit the exact identities and directed dependency relation.
2. Traverse the relation from its root and require full job coverage.
3. Start an outer item only after every incoming predecessor is complete.
4. When the test item starts, open one sibling epoch over the exact partition set.
5. Start and complete each sibling, with one debit and one named effect per completion.
6. Cross the barrier only after all siblings complete, then publish the joined output.
7. Complete the outer test item only after publication, which releases the downstream item.
8. Reconcile final carrier state, debit identity, effect identity, and output identity.

## Construction from retained parts

| Retained part | Work performed in this case |
|---|---|
| `ResourceRegistry` | Commits four job IDs and two partition IDs |
| `RelationshipGraph` | Commits the four directed outer dependency edges |
| `TraversalEngine` | Visits all jobs reachable from `compile` |
| `StepGraph` | Owns outer waiting, ready, running, and completed state |
| `ForkJoin` | Owns inner worker state, barrier state, and joined-output state |
| `Budget<Compute>` | Rejects aggregate overdraw; a separate identity check requires every declared debit |
| `ActuationPass` | Applies completed work to the allocated output resource |

The example adapters retain the published `automation-structures = "=0.3.1"` `StepGraph` and
`ForkJoin` instances. Readiness, start and completion call `StepGraph::become_ready`,
`start` and `complete`; predecessor previews call its `predecessors_complete`.
The nested epoch calls `ForkJoin::start_worker`, `complete_worker`, `barrier` and `produce_output`,
and completion previews call its `all_complete`. The adapters add trace emission, readable
state-tag projections and ordinary Rust error returns. They do not implement another carrier
state machine or establish a Rust-to-TLA refinement theorem.

The domain module supplies static labels, the frozen edge and charge declarations, event dispatch,
result projection, and the composition verifier. Those functions bind source content to retained
structures. They do not replace the carrier state machines.

## Execution structures

`StepGraph` is the outer carrier. Its predecessor guard determines when each job can start, while
its node state records the outer lifecycle.

`ForkJoin` is the inner carrier. It records both worker lifecycles, rejects an early barrier,
captures the completed worker values, and permits output only from its join phase.

The nested handoff is load-bearing. Starting `test-matrix` opens the worker epoch. Publishing the
joined test output permits `StepGraph.CompleteNode(test-matrix)`, which then permits `package` to
become ready.

`Sequential` appears only in a negative control. That control replays one valid event order through
the canonical sequential carrier and produces all six final outputs. The verifier still rejects it
because an ordered trace does not establish dependency-governed release or full sibling-barrier
state.

## Independent schedule oracle

The [reference module](../../rust/crates/formal-example-domains/src/cicd_reference.rs) imports no
catalog structures and calls no construction helper. It defines plain arrays for outer and inner
lifecycle state plus two booleans for barrier and publication state, then enumerates every enabled
event until the finite workflow is complete.

The construction schedule enumerator follows the actual `StepGraph` and `ForkJoin` transition
guards. The comparison is set equality in both directions, not sampled positive coverage.
The expected cardinality is also derived without either enumerator: the two workers have six valid
start/complete interleavings, and the two-event static-analysis chain has `C(10, 2) = 45` placements
among the eight-event test chain. Therefore the frozen contract admits `6 * 45 = 270` schedules.

| Schedule evidence | Result |
|---|---:|
| Plain-state accepted schedules | 270 |
| Carrier-derived accepted schedules | 270 |
| Missing or extra schedules | 0 |
| Accepted schedules with a result or verifier mismatch | 0 |

Both paths interpret the same frozen source contract, so a shared source misunderstanding remains
possible. Their state representations and transition implementations are separate.

## Runtime checks and controls

The runtime verifier checks exact registry IDs, exact declaration-to-carrier edges, terminal outer
and inner state, barrier-before-output order, every declared debit, every target-effect identity,
the complete output set, and presence of each load-bearing structure.

| Control | Mutation | Observation |
|---|---|---|
| Early execution | Start `package` after compilation but before both predecessors complete | `StepGraph` rejects readiness |
| Missing carrier predecessor | Remove `test-matrix -> package` only from the carrier | Final output remains green; edge-set binding rejects |
| Skipped join | Publish test output without the shared barrier | Final output remains green; `ForkJoin` terminal checks reject |
| Dropped worker completion | Fabricate one partition result without its worker lifecycle | Final output remains green; worker state and debit identity reject |
| Flatten to `Sequential` | Replay a valid order without either required carrier | Final output and debit checks remain green; carrier presence rejects |
| Bypass debit | Create the package output without its compute charge | Capacity remains green; exact debit identity rejects |
| Misdirect effect | Apply static-analysis completion to the package resource | Charge remains green; target-effect identity rejects |

The controls separate premises from outcomes. A final file set can match while the construction no
longer performs the source process that the claim names.

## Formal premise-binding model

The [TLA+ model](formal/CiCdCarrierBinding.tla) adapts the same finite premise-model pattern used by
the other systems case studies. It models the outer lifecycle, inner worker lifecycle, declared and
carrier dependency relation, barrier state, debit map, target map, and both carrier-presence facts.

The positive configuration checks:

| Invariant | Bound premise |
|---|---|
| `DependencyBinding` | Carrier predecessors equal the declared predecessors |
| `DependencyRelease` | A running or completed item has completed declared predecessors |
| `PartitionCoverage` | Join and publication states contain every completed worker |
| `BarrierOrder` | Publication follows the barrier |
| `NestedHandoff` | Outer test completion follows full inner completion and publication |
| `DebitIdentity` | Every completed charged item has its declared debit |
| `EffectBinding` | Every completed charged item targets its own output identity |
| `CarrierPresence` | Both named carriers remain present |

TLC generated 80 states and retained 43 distinct states with every positive invariant green. Eight
isolated configurations each activate one fault and check only its target invariant; all eight
produced the required violation.

The `CompleteTestEarly` configuration is formal-only hardening for `NestedHandoff`. It permits the
outer test node to complete while the inner carrier is still in its fork phase. This produces a
counterexample to the handoff invariant. The seven runtime controls remain the executable controls
listed above.

This model check explores the configured finite state space. It does not establish Rust-to-TLA refinement, arbitrary-workflow
correctness, or GitHub Actions conformance.

## Run the case

From `formal/examples/rust`, inspect and execute each claim surface:

```powershell
cargo run -p formal-example-runner --offline -- describe FEX-ASM-06
cargo run -p formal-example-runner --offline -- run FEX-DOM-CICD-01
cargo run -p formal-example-runner --offline -- run FEX-DOM-CICD-03
cargo run -p formal-example-runner --offline -- run FEX-ASM-06
```

Run representative controls:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-ASM-06 `
  --control missing-carrier-predecessor

cargo run -p formal-example-runner --offline -- run FEX-ASM-06 `
  --control flatten-to-sequential

cargo run -p formal-example-runner --offline -- run FEX-ASM-06 `
  --control bypass-debit

cargo run -p formal-example-runner --offline -- run FEX-ASM-06 `
  --control misdirect-effect
```

Accepted control names are `early-execution`, `missing-carrier-predecessor`, `skip-join`,
`drop-worker-completion`, `flatten-to-sequential`, `bypass-debit`, and `misdirect-effect`. A control
command succeeds only when construction or verification rejects the mutation for its registered
reason.

Run the focused Rust tests:

```powershell
cargo test -p formal-example-domains --offline cicd::
```

From `automation-structures`, run the formal model and isolated controls through the pinned
container:

```powershell
docker build --pull=false --tag automation-structures-proofs verification

docker run --rm --init --network none --read-only --cap-drop ALL `
  --security-opt no-new-privileges --cpus 2 --memory 4g --memory-swap 4g `
  --pids-limit 512 --volume "${PWD}:/source/automation-structure-research:ro" `
  --tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777 `
  automation-structures-proofs run --subject CiCdCarrierBinding --workers 1
```

Add `--format json` to a runner command for the schedule counts, verifier verdict, final result, and
structural event count.

## Claim limits and falsifiers

The executable and formal evidence covers one immutable successful four-job workflow with two
required partitions. `Budget<Compute>` models total work, not simultaneous runner capacity or
elapsed duration. The case makes no production-readiness or comparative-efficiency claim.

The result turns red if the plain-state and carrier schedule sets differ, an accepted schedule
omits an output, a job starts before a declared predecessor completes, a registered control passes,
or the nested barrier-to-outer-completion seam requires unclassified generic behavior.
