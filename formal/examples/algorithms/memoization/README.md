# Memoization algorithm examples

These ten artifacts instantiate the shared [Memoization](../../patterns/classical/memoization.md)
composition. Each implementation builds a finite recurrence graph and invokes the same
`run_memoization` function. The corresponding reference is separately written, imports no shared
structure code, and does not call the construction module.

| ID | Algorithm | Construction reduction | Independent reference strategy |
|---|---|---|---|
| `FEX-ALG-060` | Climbing Stairs | Sum predecessor counts | Constant-space iteration |
| `FEX-ALG-061` | House Robber | Maximum of take and skip | Constant-space prefix scan |
| `FEX-ALG-062` | Longest Increasing Subsequence | Maximum predecessor extension | Patience-sorting tails |
| `FEX-ALG-063` | Coin Change | Minimum reachable predecessor plus one | Breadth-first search over amounts |
| `FEX-ALG-064` | Word Break | Logical OR over segmentable prefixes | Breadth-first search over offsets |
| `FEX-ALG-065` | Unique Paths | Sum upper and left counts | Binomial coefficient |
| `FEX-ALG-066` | Longest Common Subsequence | Diagonal extension or maximum prefix | One-row dynamic program |
| `FEX-ALG-067` | Edit Distance | Minimum insert, delete, or replace | One-row dynamic program |
| `FEX-ALG-068` | 0/1 Knapsack | Maximum take or skip | Exhaustive subset enumeration |
| `FEX-ALG-069` | Longest Palindromic Subsequence | Inner extension or maximum shortened span | LCS against reversed text |

Each named claim test runs source examples and boundary cases plus 1,000 deterministic generated
cases. Exact typed outputs must agree. The shared structural controls are inherited by every member,
and every member adds an output-corruption control that must be detected by its reference check.

The generated streams deliberately remain reproducible and may repeat inputs. Their exact inventory
is asserted in the Rust suite:

| ID | Generated cases | Distinct generated inputs |
|---|---:|---:|
| `FEX-ALG-060` | 1,000 | 36 |
| `FEX-ALG-061` | 1,000 | 881 |
| `FEX-ALG-062` | 1,000 | 873 |
| `FEX-ALG-063` | 1,000 | 82 |
| `FEX-ALG-064` | 1,000 | 518 |
| `FEX-ALG-065` | 1,000 | 4 |
| `FEX-ALG-066` | 1,000 | 1,000 |
| `FEX-ALG-067` | 1,000 | 1,000 |
| `FEX-ALG-068` | 1,000 | 833 |
| `FEX-ALG-069` | 1,000 | 545 |

From `formal/examples/rust`, run one visible case or the whole family:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-ALG-068 --scenario baseline
cargo test -p formal-example-algorithms --offline
```

Use `describe` to inspect the materialized DAC record for an instance:

```powershell
cargo run -p formal-example-runner --offline -- describe FEX-ALG-068
```

Passing results establish exact agreement and shared-schema binding only for the registered finite
input contracts and cases. They do not establish optimal complexity, production performance,
universality, or completion of the 87-member classical algorithm corpus.
