# Level of Detail Example

Artifact IDs: `FEX-DOM-REN-03` and `FEX-ASM-01`.

The example selects one quality level per finite object under a byte budget. View weight multiplies
level utility. The deterministic result maximizes total weighted utility, then minimizes bytes, then
uses the ordered choice set as the final tie rule.

The source-domain basis is Funkhouser and Sequin's 1993 adaptive display problem: choose a level of
detail and rendering method for each object that may be visible to maximize estimated benefit under
a target frame-time cost bound. This example retains the finite per-object constrained-selection
shape but substitutes its declared byte-cost and utility contract. It does not claim frame-time,
rendering-method, or heuristic equivalence to the [primary paper](https://www.cs.princeton.edu/~funk/sig93.pdf).

The construction is:

```text
QualityHierarchy -> TraversalEngine under Budget<Bytes>
                 -> CompetitiveSelection -> AllocationSnapshot
```

The implementation invokes the capacity policy of the same `rooted_frontier` composition
used by the alternate OSPF path. It records typed events for each structure and rejects a result
unless the registered recipe and shared ordering edges occur. A separately written exhaustive selector
imports no shared structure code and computes the comparison result.

Evidence covers four named scenarios (`full-budget`, `budget-cut`, `zero-budget`, and
`view-change`), 64 deterministic generated inputs, direct-target discovery and first-plan selection
bypasses, a skipped-budget-charge control, and a missing snapshot-trace control. `FEX-ASM-01` checks
the scenario set and the reported checks.

Run the visible scenario from `formal/examples/rust`:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-DOM-REN-03 `
  --scenario budget-cut
```

The claim is limited to finite supplied quality ladders, nonnegative byte costs, pure view
scoring, deterministic identity order, and the supplied scenarios and generated cases. Rendering
engine integration, visibility determination, asset streaming, hysteresis, frame timing, visual
quality, and performance are outside the claim.
