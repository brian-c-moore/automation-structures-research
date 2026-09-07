# ALK Claims: Contracts, Authority, and Evidence

The Budget contract says admitted use must stay within capacity. A proof of that contract does
not by itself establish who controls a particular Budget instance. To issue its guarantee, an
ALK must be established as the owner of that obligation and have evidence supporting the claim.
This package demonstrates the connection for Budget and Sequential in the model, then carries
three claims through the ALK reference state machine. The result distinguishes the owner's
guarantee from the assurance available to someone relying on it.

Contract proofs and integration checks answer different questions. `Budget_Proof` establishes its safety invariant for any natural-number capacity. The Budget/Sequential example uses capacity two and two steps to check how contracts connect to actions, authority, and claim records. The configurations and assumptions are:

| Boundary | What is evaluated | What remains assumed or outside the result |
|---|---|---|
| Catalog integration example | Budget capacity and Sequential history/cursor predicates, with the real carrier actions | Capacity two, two steps, values zero or one; no crash or hidden writer |
| Progress, comparison, and diagnostic examples | Fair completion, matched histories of two carriers, and observation/detection/restoration for one persistent Budget fault | Weak fairness, coupled choices, authentic labels, atomic capture, retained snapshots, and logical-clock progress as named by each witness |
| Reference-state certificate | Effect count, success/evidence coupling, and effect-owner coupling in `ALK-SPEC-1` | One operation, two attempts, revisions one and two, and only the declared failure transitions; no implementation or deployment conformance |

The [ownership definition](claim-relative-ownership.md) supplies the complete claim frame. Ownership requires both control of decisive behavior and designation as the canonical accountable principal at that frame. A named protocol can be that principal; a TCB member or observer is not a co-owner.

## Actual contracts and authority

`ALKClaimInstantiationWitness` selects `AS-BUD-CAP` and `EX-SEQ-SERIAL`. It instantiates the
Budget and Sequential modules and evaluates their predicates. Its action-partition proof shows that
the labeled actions preserve the original interleaved transition relation and frame the other
carrier's state. Wrong-predicate, wrong-frame, and omitted-action controls exercise actual behavior.

`ALKClaimAuthorityBinding` gates those actions by the modeled controller and complete decision.
Coverage is derived from the gates, then intersected with the accountability designation. Direct
control, delegated work, complete transfer, a partial split, and protocol control have different
results. Work delegation leaves the authority where it was. Transfer changes the owner and issuer.
The partial split is unowned until one protocol controls the complete decision.

The authority proof assumes authentic actor labels, atomic gates, and no external bypass.
Implementation conformance must establish those conditions for the actual controller.

## Evidence and assurance

`ClaimEvidenceBinding` binds an evidence record to the proposition it supports and the complete
frame in which it applies. The record identifies the producer and source, how the observation
was captured and kept, and who verifies it for which claimant. It also records the mechanism
claim, the assumptions it relies on, and the outcome. Semantic premises must support the
proposition; matching tokens alone are insufficient.

Controls reject assurance about the claimant's own obligation and a second owner at one frame,
even when the evidence and one issuer remain valid.

`ALKClaimAssuranceBindingWitness` supplies those premises from the Budget/AuditSink trace. The
diagnostic gate has its own authority map. Detection and restoration are separate obligations with
separate guarantee records. Their owner-issued guarantees support the claimant's A3 or A4 assurance
about the externally controlled Budget state. A0 through A5 are different assurance classes, not a
ranking in which a larger number proves more.

Controls distinguish captured observations from continued truth, require independent producers where specified, and reject mismatched frames, propositions, issuers, and mechanism claims. The diagnostic example measures logical ticks. Wall-clock detection and recovery require separate timing and storage evidence.

## Static certificate and operational result

`ALKClaimCertificate` defines the static certificate. It reuses the canonical catalog frame and
authority definitions rather than recreating them from names. Its catalog instance remains the
two selected safety schemas. Three separate reference claims evaluate these actual predicates:

| Reference claim | Predicate in `ALKReferenceStateMachine` |
|---|---|
| `reference-effect-count` | `NoDuplicateEffect` |
| `reference-success-evidence` | `SuccessCoupled /\ CommitEvidenceCoupled` |
| `reference-owner-binding` | `EffectOwnerCoupled` |

`ALKProfilesClaimCertificate` supplies the static profile adapter.
`ALKReferenceStateMachine` carries only the certificate key and small authorization interface.
`ALKReferenceClaimView` assembles a read-only result. It includes the full certificate and current
predicate outcomes, identifies the issuer and recipient, and records accountability and A5
claimant assurance. It also records the supporting evidence and the claim's relies and TCB.
Residuals state what the result leaves unresolved.

The protocol governs the declared model transitions. Agreement among deployed members and authority over crashes, networks, or services remain implementation questions. The evidence is a model observation. The certificate owner, reference client, and legacy commit-owner label have separate roles.

The reference witness explores the original transition relation and checks that every reachable
edge is admitted by the certificate gate. It also checks that the profile adapter's structure and
execution selections match the existing profile definitions. All seven supported profile/mode
configurations retain the original state counts. A separate three-attempt configuration reports
unavailable claims rather than extending the certificate's two-attempt scope.

The compatibility ceiling labels remain a separate projection: prevention/detection/recovery are
mechanism classes, conditional is a qualifier, and lost is an outcome. None becomes an obligation
or an owner-issued guarantee merely by appearing in a set.

The certificate records the following claims as still needing evidence:

- Semantic refinement from catalog contracts to the profiles that select them.
- Implementation and deployment conformance.
- Results for failure models beyond the declared transitions.
- Wall-clock timing and eventual recovery for the reference specification.
- A demonstration that the claimed TCB is minimal.

Controls substitute a wrong profile, revision, issuer, predicate, kind-as-obligation, missing residual, or forged outcome. Each must reach the intended failing invariant while the adjacent check still holds.

## Reproduce and review

Use the pinned container and the [reproducibility guide](reproducibility.md). The focused selectors
are `--contains ALKClaim`, `--subject ALK-CLAIM-1`, and `--subject ALK-SPEC-1`. The
[formal methods directory](formal-methods.md) separates the proof, model, control, and source-binding
boundaries. A source-binding check detects a substituted integration relation; semantic truth belongs
to the named proof or finite-model result.

A complete corpus receipt identifies its exact source, runner, and selection. Its accompanying
image record identifies the toolchain. Focused results gathered while files were changing do not
substitute for those records or independent review.
