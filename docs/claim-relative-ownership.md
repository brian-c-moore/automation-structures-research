# Claim-Relative Ownership and Assurance

## One ownership model across abstraction boundaries

This document defines ownership for Automation Structures, the Execution Integrity Model (EIM), and the Automation-Layer Kernel (ALK). It applies the ownership question from cloud security to systems, components, protocols, algorithms, and individual transitions.

> At one declared claim frame, an obligation has one canonical owner or no owner.

Different abstractions can have different owners: a data owner, protocol, component, or algorithm may each own related obligations. They do not share ownership of one unchanged obligation.

This is the theory definition. The companion formal package at
`formal/assurance/ownership/ClaimRelativeOwnership*` defines the typed relations, proves their
consequences under stated premises, and exercises them with finite examples and negative controls.
The [ALK Claims guide](alk-claims.md) shows how the definition is applied to actual catalog contracts
and a reference state machine. Implementation conformance is the next stage of work.

## 1. The claim frame

Ownership depends on the obligation and the system boundary. Creating an audit record and
retaining it for a year can have different owners. Even a claim about retention changes when its
failure model changes. The claim frame makes these distinctions explicit:

$$
F = \langle
Subject,
Obligation,
Mode,
Scope,
ObservationBoundary,
AuthorityBoundary,
Claimant,
FailureModel,
Abstraction,
LifecyclePhase,
PropertyForm
\rangle
$$

| Field | What it fixes |
|---|---|
| Subject | The data, state, action, component, protocol, application, or system the claim concerns |
| Obligation | The responsibility whose fulfillment or violation is being evaluated |
| Mode | The selected alternative contract when a structure has more than one mode |
| Scope | The identities, resources, operations, time interval, and deployment covered by the claim |
| Observation boundary | Which states, events, traces, evidence, and failures the claimant can distinguish |
| Authority boundary | Which principal or named protocol can govern obligation-decisive behavior |
| Claimant | The party that will rely on the claim |
| Failure model | The faults, compromise, interference, unavailability, and partitions included in the claim |
| Abstraction | The organizational, system, component, protocol, algorithmic, or transition-level view |
| Lifecycle phase | Creation, use, transfer, retention, recovery, disposal, or another declared phase |
| Property form | Safety, liveness, evidence, relational, or a separately justified specialization |

Changing a field creates a different claim frame. Its owner may change, as may the trusted
dependencies and the claims available to each party. These results concern different claims,
so a different owner at the new frame does not contradict the original result. A refinement or
composition argument is required before a result at one frame can support a claim at another.

## 2. Core relationships

For claim frame `F`, let `Decisive(F)` be the property-specific behavior whose autonomous choice can
determine whether the obligation is fulfilled. Let `Covers(P,F)` mean that principal or named
protocol `P` controls that behavior or excludes every relevant falsifying outcome under the frame's
failure model.

The model uses a partial owner function:

$$
Owner(F) \in Principal \cup \{\bot\}
$$

with the validity rule:

$$
Owner(F) = P \Rightarrow Covers(P,F)
$$

Here, `⊥` means no valid canonical owner is established. This can mean that no principal or named
protocol covers the decisive behavior, or that an eligible controlling boundary exists without a
faithful canonical-owner designation. Record which gap prevents the owner-issued guarantee: missing
control and missing designation require different repairs. Useful enforcement and evidence may
still exist for an unowned obligation.

| Concept | Meaning in this theory |
|---|---|
| Eligible controlling boundary | A boundary that satisfies the property-specific coverage relation for the frame |
| Canonical owner | The one eligible principal, including a named protocol when applicable, designated to answer for the anchored technical claim |
| Technical accountability | Answerability for fulfilling the owned obligation; it is intrinsic to canonical ownership at the same frame |
| Contract guarantee | A mathematical consequence of a reusable contract under its assumptions; it has no deployment issuer by itself |
| Owner-issued guarantee | A claim issued by the canonical owner for an obligation it owns at the declared frame |
| Assurance | A claimant's justified confidence in a proposition about an obligation it does not own, based on named evidence, mechanisms, and limits |
| Custodian | A party performing possession, storage, handling, retention, transport, or disposal duties for another frame's owner |
| Steward | A party performing delegated policy, quality, classification, or lifecycle work without thereby becoming the data owner |
| TCB member | A mechanism whose correct behavior is a premise of the claim; membership does not create ownership |

The coverage rule establishes eligibility. The frame must also designate one eligible principal
as its canonical owner, which establishes that principal's technical accountability for the
obligation. Without a faithful designation, the obligation remains unowned and no owner-issued
guarantee receives credit. A named protocol can be the principal at one frame while its
participants own distinct obligations at their own frames. An enclosing authority boundary also
creates a different frame; it does not add a second owner to the first.

## 3. Single owner, distributed obligations

This model rejects shared ownership of one anchored obligation. What looks like shared ownership
must be resolved as one of four cases:

1. Different principals own different obligations.
2. Different principals own disjoint subjects, scopes, pieces, or lifecycle phases.
3. One named protocol is the canonical owner at the composed abstraction, while its participants own
   lower-level obligations.
4. No valid canonical owner is established, either because coverage is missing or because no
   eligible boundary is established as the canonical owner. The claimant has an ownership gap and whatever
   assurance the evidence supports; the frame receives no owner-issued guarantee.

EIM records legal and organizational roles separately. Its technical question is who controls the behavior decisive for this obligation at this frame.

## 4. Accountability, delegation, and transfer

Accountability is intrinsic to ownership: owning an obligation means being answerable for fulfilling
it. It exists whether or not the owner has issued a guarantee record. Ownership also carries the
exclusive authority to issue that obligation's guarantee; the guarantee's content remains bounded
by the stated contract, assumptions, and evidence. Technical accountability is not independently
delegable:

$$
Accountable(F) = Owner(F)
$$

Work, access, possession, and limited capabilities can be delegated. Delegation always introduces a
trust boundary that must be represented by a rely, evidence path, or assurance record. It does not
automatically transfer ownership.

| Authority result | Ownership result |
|---|---|
| The delegate performs work, but the owner still constrains every obligation-decisive outcome | Ownership and technical accountability remain with the owner; the delegate is an explicit rely |
| Complete decisive authority moves and the recipient now covers the obligation | Ownership and technical accountability transfer to the recipient |
| Decisive authority is split and no named protocol covers the whole obligation | The end-to-end obligation is unowned |
| The parties control different decisive behaviors for different obligations | Each obligation has its own owner; the result is distributed ownership, not shared ownership |

A former owner cannot continue to issue the transferred guarantee. It may guarantee narrower
obligations that remain under its authority, such as request formation, admission, encryption,
verification, monitoring, recovery, or provider selection. Its claim about the transferred
obligation is assurance.

### 4.1 Custody

Custody demonstrates why the claim frame matters. An organization can be the governance owner for
classification, permitted use, provider selection, retention policy, and risk acceptance. A cloud
provider can simultaneously be the technical owner of a distinct custody or availability obligation
because it controls the storage behavior. Relative to the governance frame it is a custodian; relative
to the custody-obligation frame it is the canonical enforcement owner.

The provider may issue its custody guarantee under the stated conditions. The organizational data owner receives that
claim as assurance and remains owner of its own selection, configuration, monitoring, and response
obligations.

## 5. Trusted computing bases

The claim frame determines the relevant trusted computing base:

$$
AuthorityBase(F) \subseteq ClaimTCB(F)
$$

$$
ExternalRelies(F) = ClaimTCB(F) \setminus AuthorityBase(F)
$$

`AuthorityBase` contains the mechanisms governed by the canonical owner. That owner can itself be a
named protocol.
`ExternalRelies` contains independently controlled mechanisms or propositions whose correct behavior
the claim assumes. Every external rely must identify its owner or remain an explicit gap, together
with the evidence and assurance supporting the reliance.

An external service belongs to a larger authority only when that authority or owning protocol governs its decisive behavior. Including the service in a diagram does not establish control.

A subject-wide TCB may be reported as a union for operations, but ownership and assurance are decided
per claim frame. Minimality is not claimed unless a separate reduction result shows that removing a
member preserves or destroys the claim as stated.

## 6. Property-specific decisive behavior

`Decisive` and `Covers` must be defined for the selected property form:

| Property form | Behavior and authority that must be investigated |
|---|---|
| Safety | Transitions that can produce a bad state, together with the authority that commits or excludes them |
| Liveness | Progress steps, scheduling, fairness, time, availability, accepted traces, and authority over indefinite omission |
| Evidence | Creation, binding, observation, custody, retention, retrieval, verification, and recovery |
| Relational | Authority over the set or relation of traces relevant to noninterference, equivalence, or another hyperproperty |

For transition-falsifiable safety obligations, check-act separation is the useful specialization. A
check licenses an act only while the checked predicate stays stable until the act commits. If an
independent authority can change the fact or outcome during that interval, the local boundary cannot
issue the prevention guarantee unless its mechanism excludes every falsifying result.

Detection and recovery do not retroactively own the failed transition. Their mechanisms can own and
guarantee separate detection and restoration obligations.

## 7. Primitives and recursive abstraction

The theory applies the same ownership rule while moving down into an implementation or up into a
system. An abstraction primitive is:

> A reusable semantic unit at the selected abstraction for which no validated composition from the
> pinned vocabulary supplies the same behavior-obligation relationship.

This is a provisional classification within the stated vocabulary and tested decompositions, not a
proof of absolute irreducibility. A faithful reduction revises the classification.

Atomicity is relative to that decomposition. A primitive can require several inseparable contract
clauses, offer alternative modes, or expose more than one genuine obligation. A formal clause is not
automatically an obligation, and the discovery process must not force one obligation shape on every
structure.

Downward refinement follows this chain:

```text
domain obligation
  -> structure schema
  -> structure instance
  -> execution contract
  -> component and protocol obligations
  -> implementation mechanisms
  -> runtime behavior and evidence
```

Each step preserves or explicitly changes the subject, obligation, decisive behavior, authority,
failure model, relies, and guarantee ceiling.

Upward composition adds seam obligations rather than merely unioning child claims:

$$
ChildGuarantees
\land SeamObligations
\land AuthorityClosure
\land DischargedRelies
\Rightarrow ParentGuarantee
$$

The parent guarantee has its own claim frame and canonical owner. If `AuthorityClosure` does not hold,
the child guarantees remain assurance inputs and the parent receives no end-to-end guarantee.

## 8. The ALK at system scale

The ALK combines selected structure and execution contracts into one governed execution plan. It instantiates their obligations, checks the responsibilities at their interfaces, and maps authority and trusted dependencies.

```text
obligation instances
+ selected structure and execution contracts
+ composition and refinement relations
+ authority and TCB partitions
+ external assurance requirements
    -> immutable governed plan
    -> static claim certificate
    -> kernel execution and evidence
```

The ALK owns obligations whose complete decisive behavior it controls. Claims about independently controlled effects, services, and custody rely on assurance from their owners.

The same ownership analysis can be applied at different abstractions. New domains may require new primitives, modes, or compositions; the discovery rules evaluate them against their behavior and obligations.

## 9. Security architecture record

For each claim, record:

| Field | Required result |
|---|---|
| Frame | Every field of the declared claim frame |
| Contract basis | Structure schema, selected mode, exact clauses, assumptions, and proof roots |
| Decisive behavior | The complete property-specific behavior that can satisfy or violate the obligation |
| Coverage | The real mechanism by which each behavior is controlled or each falsifying result is excluded |
| Canonical owner | One principal or named protocol, or `unowned` |
| Accountability | The same technical principal as the owner; separate legal and organizational roles if relevant |
| Guarantee | Issuer, recipient, proposition, scope, relies, evidence basis, TCB, and ceiling |
| Delegation and transfer | Delegated work, moved authority, former owner, new owner, and remaining local obligations |
| Assurance | Claimant, proposition, source, proposition owner when known, evidence, independence, timing, assumptions, and limits |
| Composition | Child frames, seam obligations, discharged relies, and authority closure |
| Residual | Unmodeled behavior, unowned interval, unverified rely, or other open risk |
| Falsifier | A concrete condition, trace, authority counterexample, or evidence failure that defeats the claim |

## 10. Refutation and claim boundary

The model must be revised if a faithful counterexample shows any of the following:

- Two principals must independently issue the same guarantee for one unchanged claim frame and cannot
  be represented as separate obligations, disjoint scopes, or one owning protocol.
- A non-owner can issue the same guarantee without acquiring the decisive authority.
- Ownership can be derived without identifying the behavior decisive for the selected property form.
- A higher-level guarantee follows from child guarantees without seam obligations, discharged relies,
  and authority closure.
- Redrawing an abstraction or TCB boundary is sufficient to create authority that the system does not
  possess.

The formal package proves consequences of the typed relationships under stated premises and tests them with finite witnesses and negative controls. Catalog completeness and implementation or deployment conformance require separate evidence.

## References

- [NIST information owner](https://csrc.nist.gov/glossary/term/information_owner)
- [NIST assurance](https://csrc.nist.gov/glossary/term/assurance)
- [NIST trusted computing base](https://csrc.nist.gov/glossary/term/trusted_computing_base)
- [NIST SP 800-100, Information Security Handbook](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-100.pdf)
- [Rust references and borrowing](https://doc.rust-lang.org/stable/book/ch04-02-references-and-borrowing.html)
