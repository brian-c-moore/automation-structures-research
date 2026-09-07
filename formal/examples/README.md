# Formal Examples

This package contains executable examples built from the structures described by the Automation
Structure theory. The current examples implement level-of-detail selection under a capacity limit, normalized
intra-area route selection, a domain-neutral relation between their selected-frontier stages,
preemptive earliest-deadline-first scheduling, a state-based replicated JSON object, optimistic
software transactional memory, a fixed-grid Renyi differential privacy accountant, a nested CI/CD
pipeline, and ten dynamic-programming algorithms through one executable Memoization composition.

The [manifest](manifest.json) lists the twenty-two executable artifact IDs, their claims, and their
limits. Each program returns its result together with runtime checks and a typed structural trace.

## Run the examples

Run commands from `formal/examples/rust`. The workspace pins four direct crates.io dependencies; on a machine without a populated Cargo cache, run `cargo fetch` once with network access, after which every command below works offline.

List or inspect the available artifacts:

```text
cargo run -p formal-example-runner --offline -- list
cargo run -p formal-example-runner --offline -- describe FEX-OSPF-001
```

`describe` materializes the artifact's evidence record. It reports the frozen source territory,
native problem, content-stripped roles, classified construction graph, oracle separation, controls,
claim ceiling, residuals, and falsifiers. Instance artifacts show the base record and their stored
delta instead of copying the base account.

Run the visible LOD scenario:

```text
cargo run -p formal-example-runner --offline -- run FEX-DOM-REN-03 --scenario budget-cut
```

Run the RFC 2328 route-selection fixture through either construction:

```text
cargo run -p formal-example-runner --offline -- run FEX-OSPF-001 --scenario rfc2328-rt6 --implementation rooted-frontier
cargo run -p formal-example-runner --offline -- run FEX-OSPF-001 --scenario rfc2328-rt6 --implementation conventional
```

Compare both domains and print their structural relation:

```text
cargo run -p formal-example-runner --offline -- compare FEX-XFER-LOD-OSPF-01
```

Run the shared Memoization fixture and one algorithm instance:

```text
cargo run -p formal-example-runner --offline -- run FEX-SC-C01
cargo run -p formal-example-runner --offline -- run FEX-ALG-068 --scenario baseline
```

Run the [preemptive EDF case study](case-studies/preemptive-edf/README.md):

```text
cargo run -p formal-example-runner --offline -- run FEX-DOM-RT-01
```

Run the [nested CI/CD case study](case-studies/nested-ci-cd-pipeline/README.md):

```text
cargo run -p formal-example-runner --offline -- run FEX-DOM-CICD-01
cargo run -p formal-example-runner --offline -- run FEX-DOM-CICD-03
cargo run -p formal-example-runner --offline -- run FEX-ASM-06
```

Run the other systems case studies:

```text
cargo run -p formal-example-runner --offline -- run FEX-DOM-DIST-01
cargo run -p formal-example-runner --offline -- run FEX-DOM-TXN-01
cargo run -p formal-example-runner --offline -- run FEX-DOM-PRIV-01
```

Their full accounts are in the [replicated JSON object](case-studies/state-based-json-crdt/README.md),
[optimistic STM](case-studies/optimistic-stm/README.md), and
[fixed-grid RDP accountant](case-studies/fixed-grid-rdp-accountant/README.md) case studies. Each
account records its source territory, domain-neutral decomposition, retained parts, runtime relies,
independent reference, controls, finite formal model, results, limits, and falsifiers.

Add `--format json` to any list, describe, run, or compare command for machine-readable output.

Each construction record has a separate outcome. A matching domain result supports behavioral
evidence, but it supports a catalog reconstruction only when every claim-path node is classified and
the outcome is `catalog-composition`. Unidentified reusable behavior and behavior that may exist only
at one abstraction layer have distinct candidate outcomes. Neither outcome silently changes the
catalog or passes a reconstruction claim.

## Memoization family

The [Memoization schema](patterns/classical/memoization.md) composes `ResourceRegistry`,
`TraversalEngine`, and `Reduction`. All ten [algorithm instances](algorithms/memoization/README.md)
invoke that same executable composition. Algorithm modules provide only the recurrence graph,
candidate derivation, reduction operation, input contract, and output projection.

Each instance is checked against a separately written reference over named cases and 1,000
deterministic generated cases. Three inherited bypass controls remove one shared structure at a
time and must break recipe binding while preserving the calculation. A fourth control corrupts the
completed output and must break reference agreement while leaving recipe binding green.

## Shared composition

Both domains invoke the `rooted_frontier` composition. The relation checks these four structures
and the three ordering edges between them. Each domain has a separate bypass control for every
shared edge, and every registered implementation identity must match that domain's construction
account:

| Shared structure | LOD instance | Route-selection instance |
|---|---|---|
| `QualityHierarchy` | Root-relative representation candidates | Root-relative simple-path candidates |
| `TraversalEngine` | Candidate and feasible-plan traversal | Candidate-path traversal |
| `CompetitiveSelection` | Best feasible frontier within capacity | Minimum candidate set per reachable target |
| `AllocationSnapshot` | Selected representation frontier | Selected route frontier |

LOD supplies a policy with a capacity limit under `Budget<Bytes>`. Route selection supplies a
minimum-per-target policy with equal-minimum retention and no route-slot budget. The route example
also uses `ResourceRegistry`, `RelationshipGraph`, and `Reduction` where its input preparation or
conventional Dijkstra construction requires them.

The conventional route construction and the rooted-frontier construction are separate executable
paths. The rooted-frontier path enumerates finite simple paths from the normalized topology before
the shared composition selects minimum candidates. Both paths are compared with a Bellman-Ford
reference, and the published RT6 fixture checks all 15 local-destination rows from RFC 2328 Table 2.

## Domain-neutral decomposition

Each run freezes one finite input state. After domain nouns are removed, both selection problems
contain the following roles:

| Role | Meaning |
|---|---|
| Context | Frozen origin and conditions used to evaluate candidates |
| Target | Endpoint for which the result may require a representative |
| Candidate | One possible representative for a target |
| Extension | Permitted transition that derives another candidate |
| Measure | Ordered value computed relative to the context |
| Frontier | Discovered candidates whose effect on the result is unresolved |
| Cut policy | Admission, replacement, tie, capacity, and completion rules |
| Snapshot | Committed selected frontier |

The shared transition shape is:

1. Freeze the context and input version.
2. Seed a finite frontier from the context.
3. Visit and extend candidates through permitted relations.
4. Compute or accumulate each candidate measure.
5. Compare candidates that serve the same target.
6. Apply the cut policy until remaining candidates cannot change the selected frontier.
7. Commit the selected frontier as one snapshot.

The domains supply different content at that boundary:

| Parameter | LOD | Route selection |
|---|---|---|
| Context | Observation state | Source state and topology version |
| Target | Relevant spatial element | Requested reachable endpoint |
| Candidate | Fidelity representative | Finite simple derivation from the source |
| Extension | Move along a fidelity relation | Add one relation edge without repeating a vertex |
| Measure | Contextual benefit and resource charge | Accumulated transition charge |
| Cut policy | Best feasible collection under aggregate capacity | Minimum measure per target with ties retained |
| Snapshot | Selected representation frontier | Selected route frontier |

`Buffer`, `OrderingPass`, `Accumulator`, and `Projection` remain connective forms. Candidate
generation, measures, coverage, tie handling, and update triggers remain domain parameters.

## Verify

Run the Rust workspace checks from `formal/examples/rust`:

```text
cargo test --workspace --offline
cargo clippy --workspace --all-targets --offline -- -D warnings
```

The tests cover named and generated LOD and route inputs, the RFC 2328 fixture, equal-cost next
hops, structural relation checks, all ten Memoization algorithms over 10,000 deterministic generated
cases, the five systems case studies, and faults that must make the corresponding checks fail.

The promoted case-study directories also contain TLA+ premise-binding models and isolated controls.
Their READMEs provide the pinned container selectors and exact result counts for each configuration.

## Scope

These programs demonstrate the registered constructions and cases. They do not implement a renderer or the OSPF
protocol. Claims about convergence, scheduling, transactional histories, and privacy accounting are
limited to the exact case-study contracts; no production, comparative-performance, or general
Rust-to-TLA refinement claim is made.

- `domains/rendering/` defines the LOD input, checks, and exclusions.
- `domains/networking/` defines the normalized route-selection input, checks, and exclusions.
- `rust/crates/formal-example-structures/` contains the reusable executable structures.
- `rust/crates/formal-example-domains/` contains both domain constructions and their references.
- `rust/crates/formal-example-algorithms/` contains the Memoization schema, algorithm instances,
  and independent references.
- `rust/crates/formal-example-runner/` provides list, describe, run, and compare commands.
- `case-studies/` contains the full source, DAC, evidence, control, reproduction, and claim-boundary
  accounts for the five systems examples.
