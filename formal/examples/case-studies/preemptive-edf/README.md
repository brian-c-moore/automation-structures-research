# Preemptive Earliest-Deadline-First Scheduling

Artifact ID: `FEX-DOM-RT-01`

This case study reconstructs processor-demand admission and preemptive
earliest-deadline-first dispatch from retained Automation Structures parts. It covers one processor,
integer time, independent periodic or sporadic tasks, complete preemption, declared execution
bounds, and finite executable evidence.

The result is an existing-structure composition. No new primitive, connective form, execution
structure, or named composition was needed.

## Claim

For the registered preemptive uniprocessor task model and registered finite cases, the shared-structure
construction applies finite processor-demand admission and complete-ready-set earliest-deadline
dispatch and agrees with separate admission and exhaustive-scheduling oracles, while the
mechanized premise-binding model passes its positive and isolated-control checks.

This separates two questions:

1. Do the published scheduling results state the mathematical relation between feasible demand,
   earliest-deadline dispatch, and deadline satisfaction?
2. Does this construction perform the admission, readiness, selection, effect, progress,
   and ordering operations required by that relation?

The cited scheduling literature is the authority for the first question. The executable recipe,
runtime verifier, separate references, formal model, and controls address the second.

## Source territory

The source model uses tasks described by execution demand `C`, relative deadline `D`, and period or
minimum release separation `T`. A released job has an absolute deadline `release + D`. The execution
resource can advance one ready job by one integer unit at each time position.

The source authorities are:

- [Liu and Layland, 1973](https://doi.org/10.1145/321738.321743), for the periodic hard-real-time model
  and deadline-driven uniprocessor scheduling foundation.
- [Baruah, Rosier, and Howell, 1990](https://doi.org/10.1007/BF01995675), for finite
  processor-demand analysis of integer-time periodic task systems.
- [Baruah, Mok, and Rosier, 1990](https://doi.org/10.1109/REAL.1990.128746), for preemptive
  scheduling of sporadic hard-real-time tasks on one processor.
- [Linux deadline scheduling documentation](https://docs.kernel.org/scheduler/sched-deadline.html),
  for an operational account of runtime, deadline, period, remaining runtime, admission, and
  earliest scheduling deadline.

Linux `SCHED_DEADLINE` is a source illustration, not the implementation under test. This artifact
does not model Constant Bandwidth Server replenishment, bandwidth reclaiming, kernel run queues, or
Linux system calls.

## Domain-neutral decomposition

The domain terms can be removed without changing the governing relations:

| Neutral role | Scheduling binding | Preserved relation |
|---|---|---|
| Identity | Task and released-job identity | Only admitted identities can produce governed work |
| Capacity | Processor supply over repeating and finite intervals | Projected demand cannot exceed the matching available amount |
| Eligibility | Released unfinished jobs | Every and only currently eligible item enters selection |
| Urgency | Absolute deadline with deterministic ties | The least urgency key wins among all eligible items |
| Allocation | One selected job resource | At most one eligible resource is selected per time position |
| Effect | One execution debit | The effect target is the selected resource |
| Progress | Remaining execution demand | One governed effect consumes one declared unit |
| Order | Execution quantum position | Begin precedes selection, effect, and completion |
| Observation | Deadline verdict | Expired incomplete work is observable from authoritative state |

The process is therefore:

1. Validate identities and source parameters.
2. Project required capacity over the repeating window and every finite interval in the declared
   feasibility bound.
3. Commit each projection against its matching capacity, then publish the accepted identities.
4. At each time position, derive every eligible unfinished item.
5. Select the item with the least urgency value.
6. Bind the selected identity to one effect on that same identity.
7. Debit one unit from its authoritative progress account.
8. Complete the ordered position and evaluate any expired unfinished item.

## Construction from retained parts

| Retained part | Work performed in this case |
|---|---|
| `Budget<ExecutionTicks>` | Checks repeating and finite-interval admission charges; remains the sole per-job progress authority |
| `ResourceRegistry<TaskSpec>` | Publishes exactly the task set whose complete admission recipe accepted |
| `CompetitiveSelection` | Selects the least urgency key from the complete ready set |
| `SelectThenActuate` | Carries the selected resource into the effect step without accepting a second target |
| `ActuationPass` | Records one effect on the selected job resource |
| `Sequential<Option<JobIndex>>` | Records one begin and one completion value for every execution position |
| Typed trace and recipe verifier | Checks unique per-position events, every ordering edge, and every registered commit |

`SelectThenActuate` is the existing shared-allocation composition used here. The case does not create
an EDF-specific replacement for it.

The scheduling module supplies domain content that the retained parts consume:

- Task and release validation.
- Checked greatest-common-divisor, least-common-multiple, demand, and deadline arithmetic.
- The processor-demand projection and absolute-deadline urgency key.
- Periodic release generation and validated sporadic release input.
- Deadline-miss observation and public scenario data.
- Finite collection storage and deterministic identity ordering.

These functions compute domain values or carry runtime data. None owns capacity admission,
authoritative identity, winner exclusivity, winner-to-effect identity, progress accounting, or
ordered completion.

`RelationshipGraph` and `TraversalEngine` are absent. The decomposed source process has no graph
update, reachability, frontier search, or visit obligation. Adding those structures would not
perform source work.

## How admission works

The periodic admission path computes a common repeating interval `H`. Each task charges
`C * H / T` against a `Budget` with capacity `H`. It then checks every integer interval from one
through `H + max(D)`. For interval `t`, a task contributes:

```text
0                                      when t < D
((t - D) / T + 1) * C                  otherwise
```

Every interval receives its own capacity-`t` `Budget`. The `ResourceRegistry` commit occurs only
after the repeating charge and every interval charge accept. The runtime verifier recomputes the
registered projections and checks that each `Budget` commit precedes registry publication.

The separate admission reference repeats the published arithmetic without importing the structure
library or calling the construction helpers. This detects implementation or transcription errors.
It does not independently prove the processor-demand formula, so the primary papers remain
load-bearing authorities.

## How dispatch works

At each time position, the construction releases eligible jobs, starts one `Sequential` step, and
derives every released job whose execution `Budget` has remaining capacity. The ready set is passed
to `SelectThenActuate` with the ordering key:

```text
(absolute deadline, release time, task identity, job sequence)
```

`CompetitiveSelection` chooses the minimum key. `SelectThenActuate` derives the `ActuationPass`
target from that winner. The effect closure reserves one unit from the selected job's execution
`Budget`, after which the sequential position completes with the same job resource.

The verifier reconstructs readiness from release records, declared demand, and prior dispatches.
It does not trust the candidate set captured by the selection composition. A separate
`spent == dispatches` check ties that reconstruction to the authoritative `Budget` state. Keeping
those two checks together prevents a corrupt dispatch log from becoming an alternative progress
authority.

For every non-idle position the verifier checks:

- The candidate set equals the reconstructed complete ready set.
- The composition outcome names the charged resource.
- Exactly one `Budget.Check` and one `Budget.Commit` carry `amount=1`.
- The `ActuationPass.Commit` names the selected resource.
- The dispatch record agrees with the selected job account.
- The complete structure-and-edge recipe occurs once under that position's evidence identity.
- `Sequential.Begin` precedes `Sequential.Complete`.
- Work is not omitted when reconstructed ready work exists.

## Independent executable references

The [reference module](../../rust/crates/formal-example-domains/src/references.rs) contains two
separate result paths and imports no shared structures:

- `edf_admission_reference` implements the admission calculation separately.
- `edf_exhaustive_reference` enumerates every eligible per-position choice for a finite released-job
  set and memoizes only its own search states.

The exhaustive reference does not select by earliest deadline. It asks whether any preemptive
schedule exists through the given finite horizon. Agreement therefore compares the EDF construction
with a different decision procedure, not with another spelling of the same selection loop.

## Formal premise-binding model

The [TLA+ model](formal/EdfPremiseBinding.tla) represents the same stripped process as an admission
phase followed by repeated begin, select, actuate, and complete phases. The positive model checks:

| Invariant | Construction premise |
|---|---|
| `AdmissionBinding` | Publication requires complete interval coverage and accepted capacity bounds |
| `CompleteReadySet` | Selection input equals all released unfinished work |
| `WinnerOptimality` | A non-idle winner has the least deadline and deterministic tie order |
| `WorkConservation` | Idle selection occurs exactly when the candidate set is empty |
| `EffectBinding` | The effect identity equals the selected identity |
| `UnitProgress` | Work advances by exactly one declared unit per non-idle actuation |
| `BudgetConservation` | Remaining plus spent demand equals declared demand for every job |
| `SequentialOrder` | Begin, actuation, and completion counters retain their order |

The checked model configuration has two jobs and four execution positions. TLC explored 51
generated states and 34 distinct states with all declared invariants green.

Eight isolated configurations activate one fault each. Each configuration checks its selected
claim surface and produces the required violation:

| Control | Target | Generated / distinct states |
|---|---|---:|
| Publish before admission completes | `AdmissionBinding` | 6 / 6 |
| Omit one ready item | `CompleteReadySet` | 35 / 18 |
| Reverse the urgency order | `WinnerOptimality` | 36 / 19 |
| Idle while ready work exists | `WorkConservation` | 37 / 20 |
| Apply the effect to another identity | `EffectBinding` | 37 / 20 |
| Suppress the progress debit | `UnitProgress` | 37 / 20 |
| Debit two units at one position | `UnitProgress` | 37 / 20 |
| Complete before actuation | `SequentialOrder` | 38 / 21 |

This model check explores the configured finite state space. It does not establish a Rust-to-TLA refinement theorem and does not
re-prove EDF optimality or the processor-demand results. Its role is to make the theorem premises
explicit as state relations, exercise the repeated composition, and show that the checker observes
their named breaks.

## Executable results

| Evidence | Result |
|---|---|
| Arbitrary-deadline positive set | Admitted; all in-horizon jobs completed; no miss; full structural verifier accepted |
| Valid sporadic release trace | Admitted and completed without a miss |
| Early sporadic release | Rejected before execution |
| Generated admission grid | 798 task-set pairs agreed with the separate admission calculation |
| Admitted generated members | All 271 met their deadline obligations and passed the complete structural verifier |
| Finite feasibility grid | 212 task-set pairs agreed between EDF execution and exhaustive schedule existence |
| EDF module tests | 14 passed, 0 failed |
| Formal positive model | 51 generated states, 34 distinct states, all declared invariants passed |
| Formal controls | 8 of 8 produced their required target violation |

The generated comparisons include relative deadlines below, equal to, and above their periods. The
periodic construction and exhaustive reference include the same finite job set: releases whose
absolute deadlines are at or before the declared horizon.

The 798 admission comparisons and 212 feasibility comparisons are assertions in the generated-grid
Rust tests. The default runner reports one named scenario and does not recompute either grid.

## Discriminating controls

| Fault | Why a final deadline verdict alone is insufficient | Required observation |
|---|---|---|
| Bypass admission charges | Some small prefixes can remain green despite an invalid task-set premise | Missing charges or later miss rejects the recipe |
| Keep utilization but omit interval checks | Long-run capacity can pass while a short interval is overloaded | Complete interval coverage rejects the recipe |
| Reverse urgency | The wrong order matters only on a discriminating task set | Named witness misses a deadline |
| Suppress progress | Selection and effect events can exist without work advancing | Deadline and Budget reconciliation reject the run |
| Accelerate progress | False completion can leave every deadline green | Unit charge and spent-to-dispatch checks reject the run |
| Misdirect actuation | Another ready job can complete without changing the final verdict | Shared winner-to-effect handoff is absent and the verifier rejects |
| Omit a ready candidate | A proper subset can still meet all deadlines | Independent readiness reconstruction rejects the selection premise |
| Misorder a later repeated edge | One correct early position can hide a later failure in a first-occurrence check | Per-position recipe verification rejects the later instance |

Premise controls are checked at the structural boundary. They do not wait for a defect to cause a
deadline miss. Outcome controls use a witness on which the changed behavior is observable.
The first seven rows have public runner controls. The repeated-edge row is checked by the Rust trace
regression and its paired TLA+ control, rather than by an eighth runner mutation.

## Run the case

From `formal/examples/rust`, inspect and run the positive case:

```powershell
cargo run -p formal-example-runner --offline -- describe FEX-DOM-RT-01
cargo run -p formal-example-runner --offline -- run FEX-DOM-RT-01
```

Run representative controls:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-DOM-RT-01 `
  --control utilization-only

cargo run -p formal-example-runner --offline -- run FEX-DOM-RT-01 `
  --control omit-ready-candidate

cargo run -p formal-example-runner --offline -- run FEX-DOM-RT-01 `
  --control accelerate-progress
```

Accepted control names are `bypass-admission`, `utilization-only`, `reverse-urgency`,
`suppress-progress`, `accelerate-progress`, `misdirect-actuation`, and
`omit-ready-candidate`. A control command succeeds only when the mutated run is rejected by the
recipe verifier.

Run the EDF tests:

```powershell
cargo test -p formal-example-domains --offline edf::tests
```

From the `automation-structures` directory, run the formal model and all isolated controls through
the pinned verifier container:

```powershell
docker build --pull=false --tag automation-structures-proofs verification

docker run --rm --init --network none --read-only --cap-drop ALL `
  --security-opt no-new-privileges --cpus 2 --memory 4g --memory-swap 4g `
  --pids-limit 512 --volume "${PWD}:/source/automation-structure-research:ro" `
  --tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777 `
  automation-structures-proofs run --subject EdfPremiseBinding --workers 1
```

Add `--format json` to a runner command for the complete admission certificate, dispatch records,
job accounting, per-position witnesses, and typed structural trace.

## Interpretation

The case reconstructs a standard admission-and-dispatch process with retained parts at a systems
scale. The source mathematics remains domain content. Its executable consequences enter governed
capacity, identity, selection, effect, progress, and ordering commits rather than living in an
unobserved scheduler helper.

The result also records where abstraction stops. Demand equations, deadline arithmetic, and the
meaning of a task parameter are scheduling content. The reusable shapes govern what happens to
their outputs. This distinction allows a domain equation to remain specific without treating every
equation as a new automation structure.

No missing structural shape was found. A future case would produce a candidate only if a
source-required, separately violable obligation could not be placed in a retained structure,
connective, domain function, runtime rely, or explicit residual without losing its governed state
or commit point.

## Claim limits and falsifiers

The Rust evidence covers the named cases and deterministic generated grids. The TLA+ result
covers its two-job, four-position model. The case makes no claim about Linux kernel
conformance, multiprocessor EDF, blocking, incorrect execution bounds, non-atomic scheduler state,
clock faults, context-switch cost, production readiness, or performance relative to specialized
schedulers.

The result turns red if any of the following occurs:

- Construction and separate admission disagree on a registered input.
- EDF execution and exhaustive finite schedule existence disagree on a registered job set.
- An admitted positive recipe misses a deadline or fails its complete structural verifier.
- A named premise control passes the structural verifier or formal invariant.
- A load-bearing source responsibility cannot be placed without inventing unclassified behavior.
- Source, runner, manifest, registry, or executable evidence identities drift outside the custody
  boundary.
