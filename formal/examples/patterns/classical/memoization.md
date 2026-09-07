# Memoization

`FEX-SC-C01` is the reusable executable composition used by the ten dynamic-programming examples
in this package. It treats a computation as a finite set of named states with declared predecessor
relations. A state becomes ready after every predecessor has a stored result. Its candidates are
then reduced, and the resulting value is stored once under the state identity.

The composition uses the same running implementations in every member:

| Structure | Executable responsibility |
|---|---|
| `ResourceRegistry` | Reject duplicate state identities and duplicate result stores |
| `TraversalEngine` | Visit dependency-ready states and complete after the finite frontier empties |
| `Reduction` | Combine the recurrence candidates supplied for one state |

The registered order is:

```text
ResourceRegistry.Commit -> TraversalEngine.Initialize
TraversalEngine.Visit -> Reduction.Commit
Reduction.Commit -> ResourceRegistry.Store
ResourceRegistry.Store -> TraversalEngine.Complete
```

Algorithm code supplies the state graph, candidate derivation, reduction operation, input bounds,
and result projection. The shared composition owns state scheduling and single storage. It also
emits the structural trace. This division is executable, not a correspondence inferred from
matching event names.

## Executable schema claim

The schema fixture contains two independent states and one dependent state. Its output must agree
with a direct reference. Admitted-to-stored state accounting must be complete, and the trace must
match the registered structure-and-edge recipe. Separate controls bypass each catalog structure
while preserving the fixture calculation. Every bypass must leave result agreement green and make
recipe binding red.

Run the fixture from `formal/examples/rust`:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-SC-C01
cargo test -p formal-example-algorithms --offline schema::tests::schema_claim
```

## Claim boundary

The artifact supplies executable evidence from the registered cases for the finite sequential schema. It is
not a deductive parametric proof of every recurrence, an asymptotic-complexity result, or a claim
about parallel evaluation, cache eviction, invalidation, or persistence. Each algorithm instance
has its own source boundary, recurrence binding, independent reference, cases, and oracle control.
