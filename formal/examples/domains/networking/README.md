# OSPFv2 Route-Selection Example

Artifact ID: `FEX-OSPF-001`.

The program accepts a finite, normalized, directed link-state topology whose destination set
excludes the root. It computes intra-area path costs and equal-cost next-hop sets. It retains two
visible construction paths.

The conventional path is:

```text
ResourceRegistry -> RelationshipGraph -> TraversalEngine
                  -> CompetitiveSelection -> Reduction
                  -> AllocationSnapshot
```

The rooted-frontier path enumerates finite simple-path candidates without selecting winners, then
feeds those unresolved candidates into the shared composition:

```text
RelationshipGraph -> finite candidate paths
                  -> QualityHierarchy -> TraversalEngine
                  -> CompetitiveSelection(minimum per target, retain ties)
                  -> AllocationSnapshot
```

The rooted-frontier selection, conventional Dijkstra construction, and separately written
Bellman-Ford reference all compute the result independently. The published fixture encodes the
relevant directed graph from RFC 2328 Figure 2 and Figure 3 and checks all 15 RT6 local-destination
rows against Table 2. The source authority is
[RFC 2328](https://www.rfc-editor.org/rfc/rfc2328.html), with route calculation following the
cited sections used by this example.

Evidence covers five named scenarios (`rfc2328-rt6`, `unique-shortest`, `equal-cost-next-hops`,
`unreachable-subnet`, and `topology-update`) and 96 deterministic generated topologies. Shared-input
controls mutate link cost, edge direction, and topology freshness. A conventional-only control
drops destination coverage. Rooted-frontier controls bypass shared discovery, bypass shared
selection, reverse candidate ordering, corrupt the candidate hierarchy, detach the selected-frontier
snapshot, and replace unresolved candidates with conventional winners.

Run the published fixture from `formal/examples/rust`:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-OSPF-001 `
  --scenario rfc2328-rt6 --implementation rooted-frontier
```

Run the preserved conventional path:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-OSPF-001 `
  --scenario rfc2328-rt6 --implementation conventional
```

This is a route-selection proof of concept, not an OSPF protocol implementation. Inputs are already
normalized. LSA origination, flooding, database exchange, adjacency state, aging, authentication,
inter-area routes, external routes, convergence timing, forwarding installation, and deployment are
outside the claim. Exhaustive simple-path enumeration is construction evidence for these topologies rather than
a routing-performance claim. `Budget<Bytes>` remains an LOD-only obligation.
