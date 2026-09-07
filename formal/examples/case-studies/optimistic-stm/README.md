# Optimistic Software Transactional Memory

Artifact ID: `FEX-DOM-TXN-01`

This case study reconstructs a finite optimistic software transactional memory manager from
retained Automation Structures parts. The target covers mediated signed-integer word access,
nonnested transactions, buffered writes, stable reads, conflict abort, complete write-batch
publication, and opaque finite histories.

The result is an existing-structure composition above one explicit runtime rely. No new primitive,
connective form, execution structure, or named composition was needed.

## Claim

For the registered finite word heaps, nonnested transaction declarations, and registered finite schedules,
the shared-structure construction provides stable-epoch reads, conflict abort, and complete
target-bound write publication, and it produces histories accepted by a separate opacity evaluator;
the mechanized premise-binding model passes its positive and isolated-control checks.

The evidence separates four questions:

1. Which source behavior defines a transaction and an opaque history?
2. Which single-word atomic operation must the runtime supply?
3. Does the construction bind transaction identity, declared access, validation, write targets,
   publication, abort, and execution order to the retained parts?
4. Does each recorded history have a real-time-respecting sequential explanation?

The transactional-memory and opacity papers answer the source questions. The Rust construction,
formal model, and fault controls bind the implementation premises. A structure-free exhaustive
evaluator answers the finite history question.

## Source territory

The source authorities are:

- [Herlihy and Moss, 1993](https://doi.org/10.1145/165123.165164), for the transaction abstraction
  and atomic multi-word read-modify-write behavior.
- [Shavit and Touitou, 1995](https://doi.org/10.1145/224964.224987), for software transactional
  memory above single-word atomic synchronization.
- [Dice, Shalev, and Shavit, 2006](https://doi.org/10.1007/11864219_14), for the global-version-clock
  route in TL2 and its read validation and commit publication pattern.
- [Guerraoui and Kapalka, 2008](https://doi.org/10.1145/1345206.1345233), for opacity as a safety
  property that includes observations made by transactions that later abort.

This artifact is not a TL2 implementation. It selects a smaller global-epoch protocol that exposes
the same source obligations at a finite boundary: an even epoch permits stable reads, an odd epoch
marks one writer's complete publication window, stale writers abort, and the next even epoch makes
the complete batch visible.

## Exact object model

The shared heap is a finite map from registered cell identities to signed 64-bit integers. A
transaction declaration assigns each accessible cell one of three modes: read, write, or read-write.
Every heap access must pass through the transaction manager.

A transaction starts only at an even epoch and records that value. Reads accept a heap value only
when equal even epoch values surround the load. Writes remain in a transaction-local buffer. A
writer commits by comparing the current even epoch with its start epoch, changing the epoch to odd,
applying its complete declared target set, and publishing the next even epoch. A failed comparison
aborts without a heap effect.

The single atomic epoch word is a declared runtime boundary. The construction uses standard
`AtomicU64` load, compare-exchange, and store operations with sequentially consistent ordering.
The artifact does not derive those operations from catalog structures or claim a weak-memory proof.

## Domain-neutral decomposition

| Neutral role | STM binding | Preserved relation |
|---|---|---|
| Identity | Cell and transaction identity | A begun transaction and heap cell retain one registered identity |
| Declared relation | Transaction-to-cell access edge | Every read and write remains inside the declared access graph |
| Local proposal | Read observations and buffered writes | Speculative work remains local until accepted publication |
| Shared marker | Global even or odd epoch | Stable access and exclusive publication refer to one runtime word |
| Validation | Start epoch against current epoch | Stale work aborts before a shared effect |
| Effect batch | Buffered write targets | Every accepted write reaches exactly the declared target set |
| Publication | Next even epoch | Readers can accept the new state only after the complete batch |
| Execution order | Finite microstep interleaving | Each machine step has one registered begin and completion order |
| Observation | Serial replay respecting real time | Every transaction observation has one legal state explanation |

The stripped process is:

1. Register each cell and declared transaction-to-cell relation.
2. Begin a transaction under a fresh identity and capture the current even epoch.
3. Read only declared cells, with the same even epoch before and after the heap load.
4. Buffer declared writes without changing the shared heap.
5. Acquire publication by changing the unchanged start epoch from even to odd.
6. Build one target allocation from the complete buffered write set.
7. Apply every allocated effect while the epoch remains odd.
8. Publish the next even epoch and record commit, or abort without a shared effect.
9. Compare the recorded history and final heap with the separate opacity evaluator.

## Construction from retained parts

| Retained part or form | Work performed in this case |
|---|---|
| `ResourceRegistry` | Registers heap cells and begun transactions without replacement |
| `RelationshipGraph` | Stores the exact declared transaction-to-cell access relation |
| `ActuationPass` | Carries every buffered write target into one complete effect batch |
| `Sequential` | Records one finite transaction-microstep interleaving |
| Buffer connective | Holds transaction-local read observations and pending writes |
| Marker and Counter connectives | Carry transaction status, start epoch, and global epoch values |
| Standard `AtomicU64` runtime | Supplies the single-word acquisition and publication boundary |
| Typed trace and verifier | Checks each registered premise and exact step order |

The domain module supplies the selected global-epoch protocol, transaction status transitions,
read-own-write behavior, conflict-abort policy, and finite schedule interpreter. Those functions are
the STM solution under test. Their persistent identities, relations, effects, and execution order
remain bound to imported structures.

`BacktrackingTraversal` is absent because speculative writes never reach the heap before commit;
abort discards a local buffer rather than traversing a shared undo log. `Budget` is absent because
the target states no capacity or conservation claim. `CompetitiveSelection` is absent because the
epoch comparison defines validation and abort, not a ranked candidate allocation.

## Execution modality and concurrency

`Sequential` records one machine-executable interleaving of transaction microsteps. It does not
supply the serial transaction order used to judge correctness. Transaction overlap comes from
begin and end positions in the recorded history; the separate evaluator searches for a legal
serialization after the run.

The generated test enumerates all 924 interleavings of two six-step transaction programs while
preserving each program's local order. Every resulting history passes both the construction
verifier and the separate opacity evaluator. This directly checks that the single-process execution structure
does not erase the conflicting schedules that the target must handle.

## Independent executable reference

The [reference module](../../rust/crates/formal-example-domains/src/stm_reference.rs) imports no
shared structure and calls no construction helper. `evaluate_opacity` takes only the initial heap,
final heap, and public transaction records. It enumerates transaction orders, removes orders that
violate observed real-time precedence, and replays every read and local write against a plain map.
Only committed writes enter the replayed final heap.

The evaluator includes aborted and incomplete transactions because their observations still need a
legal sequential explanation. Acceptance requires one legal order and exact final-heap equality.
It can detect torn reads, stale conflicting commits, partial or misdirected publication, and heap
effects attributed to an aborted transaction.

The construction and reference share transaction record types and observed operation values. They
do not share epoch validation, access-graph state, effect allocation, structure traces, or commit
logic. The evaluator is exhaustive only for the finite transaction set supplied to it.

## Formal premise-binding model

The [TLA+ model](formal/StmPremiseBinding.tla) strips the process to two cells, one writer, one
reader, one epoch word with a fixed value range, and the writer's acquire-apply-publish sequence.

| Invariant | Construction premise |
|---|---|
| `IdentityBinding` | An active transaction has its own registered identity |
| `AccessBinding` | Read and applied cells remain inside the declared relation |
| `AcquisitionBinding` | Publication acquisition uses the transaction's unchanged even start epoch |
| `OddEpochExclusion` | An acquired writer keeps the shared epoch odd |
| `TargetBinding` | Every applied effect reaches the named cell |
| `PublicationBinding` | An even publication follows the complete cell set and advances the epoch once |
| `AbortNoninterference` | An aborted writer leaves no applied cell or heap effect |
| `StableReaderSnapshot` | A committed reader observes one complete two-cell state |
| `SequentialOrder` | Effects and commit remain after their required predecessor states |

The positive configuration explored 136 generated and 82 distinct states with all declared
invariants green. Eight isolated controls produced their required target violations:

| Control | Target | Generated / distinct states |
|---|---|---:|
| Reuse one transaction identity | `IdentityBinding` | 3 / 3 |
| Read outside the declared access set | `AccessBinding` | 8 / 7 |
| Acquire from a stale epoch | `AcquisitionBinding` | 17 / 14 |
| Apply one write to another cell | `TargetBinding` | 13 / 12 |
| Publish before the complete write set | `PublicationBinding` | 31 / 24 |
| Abort after one heap effect | `AbortNoninterference` | 13 / 12 |
| Accept a torn reader snapshot | `StableReaderSnapshot` | 84 / 53 |
| Commit without publication | `SequentialOrder` | 15 / 14 |

The positive configuration does not reach the antecedent of `AbortNoninterference`. Its paired
abort-after-write control reaches that state and is required to violate the invariant; the positive
run alone supplies no evidence for the abort case.

This model check explores the configured finite state space. It does not provide a Rust-to-TLA refinement theorem, prove the
single-word runtime primitive, or re-prove general opacity. The cited sources remain authority for
the general abstraction and the formal model checks whether this finite construction can bypass
the premises on which its claim depends.

## Executable results

| Evidence | Result |
|---|---|
| Two-cell atomic-pair case | Reader aborts rather than observing a partial writer batch |
| Conflicting writers | Exactly one stale-start writer can commit |
| Generated schedules | All 924 local-order-preserving interleavings pass complete verification |
| Separate evaluator | Every accepted history has a real-time-respecting serialization and exact final heap |
| Executable controls | 8 of 8 are rejected as intended |
| STM module tests | 7 passed, 0 failed |
| Formal positive model | 136 generated states, 82 distinct states, all declared invariants passed |
| Formal controls | 8 of 8 produced their required target violation |

The default runner case begins a reader and writer at epoch zero. The writer commits `(x, y) =
(1, 1)` as one publication batch. The overlapping reader aborts after the epoch changes, the final
heap is `(1, 1)`, and the separate evaluator accepts the history.

## Discriminating executable controls

| Fault | Required observation |
|---|---|
| Reuse transaction identity | `ResourceRegistry` rejects the replacement |
| Undeclared access | Access-graph reconstruction rejects the operation |
| Ignore epoch validation | A torn read appears and the opacity evaluator rejects the history |
| Allow conflicting stale commit | Acquisition identity or final serialization fails |
| Omit write target | Exact write-set and final-state checks fail |
| Misdirect write | Target identity or the final-state reference fails |
| Publish before all writes | A reader can observe a torn state and premise verification fails |
| Abort after one applied write | Abort noninterference and final-state equality fail |

The torn-read controls are outcome witnesses for premise violations. Access identity, epoch
acquisition, target coverage, publication order, and abort noninterference are also checked
directly, so a favorable endpoint cannot supply credit for a construction that bypassed them.

## Run the case

From `formal/examples/rust`, inspect and run the default case:

```powershell
cargo run -p formal-example-runner --offline -- describe FEX-DOM-TXN-01
cargo run -p formal-example-runner --offline -- run FEX-DOM-TXN-01
```

Run another positive scenario and representative controls:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-DOM-TXN-01 `
  --scenario conflicting-writers

cargo run -p formal-example-runner --offline -- run FEX-DOM-TXN-01 `
  --control ignore-epoch-validation

cargo run -p formal-example-runner --offline -- run FEX-DOM-TXN-01 `
  --control publish-before-all-writes
```

Scenario names are `atomic-pair`, `conflicting-writers`, `early-publication`, and
`undeclared-access`. The first three have an accepted honest construction. `undeclared-access` is a
negative witness that reaches its intended construction rejection when paired with the
`undeclared-access` control.

Control names are `reuse-transaction-identity`, `undeclared-access`, `ignore-epoch-validation`,
`allow-conflicting-commit`, `omit-write-target`, `misdirect-write`, `publish-before-all-writes`, and
`partial-abort-after-write`. A control command succeeds only when construction or verification
rejects the mutation.

Run the STM tests:

```powershell
cargo test -p formal-example-domains --offline stm::tests
```

From the `automation-structures` directory, run the model and all isolated controls through the
pinned verifier container:

```powershell
docker build --pull=false --tag automation-structures-proofs verification

docker run --rm --init --network none --read-only --cap-drop ALL `
  --security-opt no-new-privileges --cpus 2 --memory 4g --memory-swap 4g `
  --pids-limit 512 --volume "${PWD}:/source/automation-structure-research:ro" `
  --tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777 `
  automation-structures-proofs run --subject StmPremiseBinding --workers 1
```

Add `--format json` to a runner command for the complete public evidence record and summarized run
data.

## Interpretation

This case reconstructs a multi-word atomic-appearance protocol from retained identity,
relationship, target-effect, and execution-order structures. The selected epoch protocol remains
domain content, while one atomic epoch word supplies the irreducible runtime transition already
allowed by the theory's atomicity boundary.

No missing structural shape was found. The experiment does identify a clear seam: if the runtime
cannot provide one atomic compare-exchange and ordered publication word, the recipe loses its
acquisition boundary. Above that rely, stable reads and multi-cell publication arise from the
composition of retained parts plus the source-domain protocol.

## Claim limits and falsifiers

The executable evidence covers registered finite heaps, transaction programs, and
schedules. The TLA+ result covers two cells, one writer, one reader, and a small epoch range.
The case makes no claim about production concurrency, weak-memory correctness, lock freedom,
starvation freedom, nesting, memory reclamation, irrevocable effects, crash recovery, persistence,
distributed transactions, or performance relative to specialized STM implementations.

The result turns red if any of the following occurs:

- A positive history lacks a real-time-respecting serialization with the exact final heap.
- A transaction reads or writes outside its declared access relation.
- A writer publishes from a stale epoch or a reader accepts across an epoch change.
- The accepted effect set differs from the complete buffered write target set.
- An aborted transaction changes the shared heap.
- A named executable control passes the complete verifier.
- The formal positive model fails a declared invariant or a paired control misses its target.
- A source-required governed state or commit cannot be placed without inventing unclassified
  behavior.
