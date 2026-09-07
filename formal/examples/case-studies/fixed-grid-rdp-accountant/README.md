# Fixed-Grid Renyi Differential Privacy Accountant

Artifact ID: `FEX-DOM-PRIV-01`

This case study reconstructs a fixed-grid Renyi differential privacy (RDP) accountant from
retained Automation Structures parts. It composes certified loss at each registered order, converts
the cumulative curve to a reported `(epsilon, delta)` bound, selects the least registered bound,
enforces a hard account ceiling, and binds one accepted release to one account and query identity.

The result is an existing-structure composition. No new primitive, connective form, execution
structure, or named composition was needed.

## Claim

For the registered fixed order grid, integer scale, target delta, certified query declarations, and
registered finite workloads, the shared-structure construction composes every coordinate, selects and
enforces the registered reported bound, and agrees with a separate prefix evaluator, while the
mechanized premise-binding model passes its positive and isolated-control checks.

The claim is conditional. It separates the privacy result from the construction checks:

| Question | Evidence |
|---|---|
| What privacy result follows from valid per-query RDP guarantees and the published composition and conversion theorems? | The cited privacy literature |
| Does this construction charge every declared coordinate, perform the registered conversion over the complete grid, choose the least candidate, and enforce the selected ceiling? | The executable recipe, separate prefix evaluator, finite formal model, and controls |
| Does every accepted release have exactly one account, certificate identity, ordered prefix position, and target-bound commit while every rejection leaves state unchanged? | The executable recipe, separate prefix evaluator, finite formal model, and controls |

## Source territory

The source authorities are:

- [Mironov, 2017](https://doi.org/10.1109/CSF.2017.11), for additive composition at a fixed Renyi
  order and conversion of an RDP guarantee to an `(epsilon, delta)` differential privacy bound.
- [Dwork and Roth, 2014](https://doi.org/10.1561/0400000042), for the differential privacy
  definition and sound additive basic composition.

The selected account configuration is:

- Orders `A = {2, 3, 5, 9, 17, 33}`.
- Integer scale `S = 1,000,000` units per epsilon.
- Target `delta = exp(-24)`, so `log(1/delta) = 24`.
- One account-specific reported-epsilon ceiling.
- One certified RDP-cost coordinate for every query and registered order.

For accepted queries `Q` and order `alpha`, the cumulative coordinate is:

```text
R_Q(alpha) = sum(query.cost(alpha) for query in Q)
```

For a nonempty accepted prefix, the registered report is:

```text
reported_Q = min over alpha in A of
             R_Q(alpha) + 24 * S / (alpha - 1)
```

The selected orders make every penalty integral at scale `S`. Ties choose the lower order for a
deterministic executable observation. The empty account reports zero. A query is accepted only when
the proposed report does not exceed the account ceiling.

The order-ledger capacities are numeric representation bounds. They are not the privacy policy.
The final reported-epsilon `Budget` carries the hard account ceiling.

## Source correction retained by the artifact

A pure epsilon-DP account that adds epsilon values is a sound basic-composition account, although it
may be conservative. It is therefore not an inherently incorrect scalar control.

This case uses a sharper target: add the certified RDP cost separately at every registered order,
convert the cumulative coordinates, and select the least converted bound. The control that sums
standalone per-query converted bounds is rejected because it is not equivalent to this registered
account, not because the artifact claims that conservative basic composition is unsafe.

## Domain-neutral decomposition

| Neutral role | Privacy-account binding | Preserved relation |
|---|---|---|
| Governed identity | Account and query identities | One accepted effect maps to one authority and one certificate |
| Parallel ledgers | One cumulative value per order | Every accepted item contributes its declared amount to every coordinate |
| Projection | Conversion at one order | Governed coordinate state maps to one claim candidate at the fixed delta |
| Quality order | Converted epsilon and alpha tie key | The least registered candidate is selected deterministically |
| Hard capacity | Reported epsilon ceiling | A selected candidate cannot commit above the account limit |
| Effect target | Named account | All accepted state changes one selected account |
| Execution order | Adaptive request prefix | A later certificate may depend on earlier released results |
| Evidence relation | Certificate, charges, bound, and release | Every accepted effect has one cross-checked account |

The stripped process is:

1. Resolve the request's account and validate its query identity and complete fixed-order curve.
2. Begin one ordered request position.
3. Extend every candidate fixed-order total by the declared coordinate cost.
4. Convert every candidate total with the registered penalty.
5. Select the least converted candidate from the complete order set.
6. Reject without mutation if the proposed report exceeds the hard ceiling.
7. Otherwise charge every coordinate ledger and the report increase.
8. Register the accepted query identity, apply the completed candidate state to the named account,
   authorize one release, and complete the request position.
9. Reconstruct every accepted prefix without reading the construction's structure state.

## Construction from retained parts

| Retained part | Work performed in this case |
|---|---|
| `ResourceRegistry` | Registers account identities and account-local accepted query identities |
| `Budget<RdpMicroEpsilon>` | Carries one exact additive ledger for each registered order |
| `CompetitiveSelection` | Selects the least converted bound from the complete order set |
| `Budget<ReportedMicroEpsilon>` | Enforces the hard reported-epsilon ceiling |
| `ActuationPass` | Binds the fully constructed candidate replacement to the requested account |
| `Sequential` | Records the adaptive request prefix and accepted or rejected completion order |
| Typed trace and recipe verifier | Checks every individual request edge and cross-ledger identity |

The domain module supplies:

- Fixed orders, integer scale, target delta, and query-curve validation.
- Checked coordinate addition and the RDP-to-DP projection.
- Deterministic candidate tie ordering.
- Finite account and request storage.
- The certificate, mediation, and runtime atomic-replacement relies.

The nonlinear reported result does not require nonlinear persistent state. The persistent inputs are
six additive ledgers. Conversion is a stateless projection over them. The minimum is an existing
selection. The hard output is another existing capacity account.

`FederatedBudget` is absent because the order coordinates are alternative views of the same
declared privacy loss, not subpools allocated under one master capacity. `Reduction` is absent
because each coordinate `Budget` is already the sole persistent accumulator for that coordinate.

## Execution modality

`Sequential` is source-faithful at this boundary. The selected composition permits an adaptive
sequence in which a later certified mechanism depends on earlier released outputs. The observed
claim is over one ordered accepted prefix. It has no parallel branch lifecycle, join barrier,
message-delivery, or flow-control obligation.

The execution structure records the logical accounting order. Production serialization and atomic replacement
of one completed account candidate remain explicit runtime relies.

## Capacity and projection are different obligations

The most discriminating control drops the `log(1/delta)/(alpha - 1)` penalty. Every fixed-order
ledger and the reported-epsilon ledger remain within capacity because the wrong projection makes
the charges smaller. The complete verifier still rejects the first candidate set.

That result establishes an important boundary:

> A capacity structure can establish that the quantity it received did not exceed capacity. It
> cannot establish that the projection which produced that quantity is the source-authorized
> projection.

The artifact therefore binds both obligations:

- `Budget` owns capacity conservation and rejection.
- A separate prefix evaluator owns formula-instance, complete-candidate, and decision fidelity.

The evaluator is independent of construction structure state, but it is not an independent proof
of Mironov's theorem. Construction and evaluator separately transcribe the same closed-form
conversion. A shared transcription error can escape both, so the primary paper remains the formula
authority.

## Independent executable reference

The [reference module](../../rust/crates/formal-example-domains/src/rdp_reference.rs) imports no
shared structure and calls no construction helper. `evaluate_prefix` reads only the fixed
configuration and accepted query declarations. For every prefix it independently:

1. Sums each registered coordinate.
2. Converts every order using the configured penalty.
3. Selects the minimum epsilon with the declared tie rule.
4. Returns the complete candidate set, report, and winning order.

The construction verifier compares every accepted-prefix curve, candidate set, winner, report,
decision, final account, query registry, and release count with this result. Rejected requests are
checked by full before-and-after account equality.

## Formal premise-binding model

The [TLA+ model](formal/RdpPremiseBinding.tla) uses two accounts, two fixed orders, and two requests:
one accepted request followed by one hard-ceiling rejection. The configured penalty is treated as a
source premise. The model checks how that premise enters the executable account; it does not derive
the penalty from the privacy theorem.

| Invariant | Construction premise |
|---|---|
| `ProjectionBinding` | Every candidate equals its cumulative coordinate plus the configured penalty |
| `CompleteCandidateSet` | Selection receives every registered order |
| `WinnerOptimality` | The selected order has the least candidate bound with deterministic ties |
| `CoordinateBinding` | An accepted account stores the complete candidate coordinate curve |
| `HardCapacity` | No account report or accepted proposal exceeds the ceiling |
| `QueryIdentityBinding` | One account does not accept the same query identity twice |
| `TargetBinding` | Only the named account changes on acceptance |
| `RejectionNoninterference` | A rejected request changes no account state |
| `ReleaseBinding` | One accepted decision adds one release; rejection adds none |
| `SequentialOrder` | Begin, selection, decision, and completion retain their order |

The positive configuration explored 12 generated and 12 distinct states. Nine isolated controls
produced their required target violations:

| Control | Target | Generated / distinct states |
|---|---|---:|
| Reuse an accepted query identity | `QueryIdentityBinding` | 10 / 10 |
| Omit one coordinate charge | `CoordinateBinding` | 5 / 5 |
| Drop the configured conversion penalty | `ProjectionBinding` | 3 / 3 |
| Omit the true minimum candidate | `CompleteCandidateSet` | 3 / 3 |
| Reverse the candidate order | `WinnerOptimality` | 4 / 4 |
| Accept above the hard ceiling | `HardCapacity` | 10 / 10 |
| Apply an accepted account to another target | `TargetBinding` | 5 / 5 |
| Mutate state after rejection | `RejectionNoninterference` | 10 / 10 |
| Complete before a decision | `SequentialOrder` | 6 / 6 |

The positive model is one deterministic finite request trace. The isolated control configurations
exercise registered breaks of that trace; the model is not coverage of every request ordering.

This model check explores the configured finite state space. It does not prove certificate truth, total mediation, the privacy
theorem, the conversion formula, runtime atomicity, or a Rust-to-TLA refinement relation.

## Executable results

| Evidence | Result |
|---|---|
| Demonstration stream | 7 requests across two accounts; 6 accepted and 1 rejected |
| `scope-a` accepted prefix | Winning orders `17, 17, 17, 9` |
| `scope-a` final report | Epsilon `4.8` at order `9` under ceiling `5.0` |
| Hard-ceiling rejection | Fifth `scope-a` request rejected with both account states unchanged |
| `scope-b` account | 2 accepted queries; epsilon `2.35` at order `17` |
| Generated workload grid | 90 configurations and 315 independently recomputed decisions agreed |
| Certificate shape | Malformed order width rejected |
| Account-local identity | The same query ID accepted once in each distinct account |
| Executable controls | 10 of 10 were rejected as intended |
| RDP module tests | 7 passed, 0 failed |
| Formal positive model | 12 generated states, 12 distinct states, all declared invariants passed |
| Formal controls | 9 of 9 produced their required target violation |

## Discriminating executable controls

| Fault | Required observation |
|---|---|
| Reuse query identity | Account-local registry rejects replacement |
| Omit one order charge | Separate curve and cross-ledger checks fail |
| Double one order charge | Separate curve and report checks fail |
| Drop the delta penalty | Projection check fails while capacity remains green |
| Omit the best order | Complete-candidate and winner checks fail |
| Sum standalone converted bounds | Prefix evaluator rejects a conservative but non-equivalent account |
| Bypass the reported `Budget` | Capacity, decision, and ledger identities fail |
| Misdirect the account | Target binding and account isolation fail |
| Mutate rejected state | Full rejection noninterference fails |
| Misorder a later commit | Per-request recipe verification rejects the later instance |

The standalone-bound control accepts two `scope-a` queries where the registered RDP account accepts
four. Both capacity ledgers remain green. The verifier rejects the mutation because it does not
implement this case's selected claim.

## Run the case

From `formal/examples/rust`, inspect and run the demonstration:

```powershell
cargo run -p formal-example-runner --offline -- describe FEX-DOM-PRIV-01
cargo run -p formal-example-runner --offline -- run FEX-DOM-PRIV-01
```

Run representative controls:

```powershell
cargo run -p formal-example-runner --offline -- run FEX-DOM-PRIV-01 `
  --control drop-delta-penalty

cargo run -p formal-example-runner --offline -- run FEX-DOM-PRIV-01 `
  --control omit-best-order

cargo run -p formal-example-runner --offline -- run FEX-DOM-PRIV-01 `
  --control mutate-rejected-state
```

Control names are `reuse-query-identity`, `omit-order-charge`, `double-order-charge`,
`drop-delta-penalty`, `omit-best-order`, `sum-standalone-bounds`, `bypass-reported-budget`,
`misdirect-account`, `mutate-rejected-state`, and `misorder-later-commit`. A control command
succeeds only when construction or verification rejects the mutation.

Run the RDP tests:

```powershell
cargo test -p formal-example-domains --offline rdp::tests
```

From the `automation-structures` directory, run the model and all isolated controls through the
pinned verifier container:

```powershell
docker build --pull=false --tag automation-structures-proofs verification

docker run --rm --init --network none --read-only --cap-drop ALL `
  --security-opt no-new-privileges --cpus 2 --memory 4g --memory-swap 4g `
  --pids-limit 512 --volume "${PWD}:/source/automation-structure-research:ro" `
  --tmpfs /work:rw,exec,nosuid,nodev,size=2g,mode=1777 `
  automation-structures-proofs run --subject RdpPremiseBinding --workers 1
```

Add `--format json` to a runner command for the complete public evidence record and summarized run
data.

## Interpretation

This case reconstructs a theorem-bound accounting process whose system-level report is nonlinear
while its persistent coordinates remain additive. The mathematical content does not disappear;
it enters the construction as a declared projection over governed state. The retained parts own
identity, coordinate capacity, minimum selection, hard output capacity, target effect, and prefix
order. The verifier separately owns fidelity to the registered projection.

No missing structural shape was found. A reusable fixed-grid accountant theorem package might
eventually reduce repeated evidence work, but one occurrence does not justify a new catalog entry.

## Claim limits and falsifiers

The executable evidence covers the demonstration and generated workload grid. The TLA+
result covers two accounts, two orders, and two requests. The case does not establish that a
mechanism is differentially private, that a supplied RDP certificate is true, that every production
release is mediated, or that the fixed order grid gives the continuous optimum. It makes no
efficiency, utility, performance, production-readiness, or universality claim.

The result turns red if any of the following occurs:

- Any accepted coordinate, converted candidate, winner, report, decision, or final account differs
  from the separate prefix evaluator.
- A query commits above its hard ceiling, changes another account, or mutates state after rejection.
- A named executable control passes the complete verifier.
- The formal positive model fails a declared invariant or a paired control misses its target.
- Source review finds that the registered conversion differs from the cited theorem.
- A source-required governed state or commit cannot be placed without inventing unclassified
  behavior.
