# Automation Structures

## Status

Experimental and Open Research

---

Automation Structures provides a catalog of reusable state-machine abstractions, organized around behavioral obligations, with explicit contracts and conditions for composition.

The theory explains why these abstractions were selected and how their contracts hold when
combined. The [reference](docs/reference.md) lists the parts; the
[introduction](docs/introduction.md#state-and-behavior) explains the state-machine model and
obligation boundary.

## Build with the Structures

Use [`automation-structures`](https://github.com/brian-c-moore/automation-structures) for the Rust
implementations. The [quick start](https://github.com/brian-c-moore/automation-structures#quick-start)
shows how a Budget reserves capacity before an allocation. Build with the checked operations and
compositions, then supply your domain logic.

`alk-core` is being built as an automation kernel using the same library for its execution
machinery and developers' components and flows. Its
[roadmap](ROADMAP.md#implementation-and-further-research) records the remaining integration and
conformance work.

## Why I Built This

This started with an automation platform I wanted to build. I wanted to identify the patterns
necessary to automate across domains and understand the different ways work executes. After the
fifth or sixth prototype, I started seeing patterns that fit the system I had in mind. I still had
questions about what made them useful building blocks and whether their guarantees would hold
when assembled. This research is my attempt to answer those questions.

Security work also supplies a personal motivation. As a security professional I am required to be
able to decompose any system, in any domain, at any and every layer of the stack. No other role
carries that requirement in the same way, and the only way it is remotely feasible is to identify
where systems are structurally similar and chunk them. The same move is how I avoid rederiving
solutions other domains have already established: I don't need to be an expert in every domain
to recognize a budget, a registry, an audit log, or a competitive selection when I see one.

## Core Ideas

A CPU budget and a spending budget apply the same rule to different resources: admitted use must
stay within capacity. A budget governs whether another allocation can proceed. If two callers
can each pass a capacity check and then spend the same remaining capacity, the system has failed
to keep that promise. The Budget structure gives that responsibility a reusable contract. The
check must remain valid until the allocation takes effect. A particular system supplies the
resource and the conditions under which that contract must hold.

Think of building construction: materials and layouts vary, but a design still has to carry its
loads through sound members and joints. Automation Structures collects recurring obligations and
ways to connect the parts that carry them. The formal work checks the modeled parts and assemblies
under their stated assumptions.

When one component hands work to another, the design also has to account for what each controls
and what can fail between them. That is part of the construction, alongside the choice of how the
work runs.

Work dependencies and execution are separate choices. Knowing which steps depend on others does
not settle how the runtime should advance them. It might finish one step before starting the next,
run workers that meet at a barrier, or stream results between active operators. The
[execution structures](docs/execution-structures.md) describe those behaviors and the obligations
that come with them.

## A Shared Construction

The rendering and routing examples test how much of a construction can be reused across domains.
The rendering example chooses a detail level for each object to maximize its declared quality
score within a byte budget. The routing example chooses minimum-cost routes to reachable targets
and retains equal-cost alternatives.

Both run the same `rooted_frontier` composition. It organizes candidates, traverses them, selects
the accepted set, and records a snapshot. Rendering adds a budget; routing has no route-slot limit.
Each example has controls that bypass the connections between the shared structures. The check
must catch each broken connection.

The [LOD/OSPF example](formal/examples/README.md#shared-composition) shows the construction and how
it is checked. Its scope is the selection problem, not a complete renderer or OSPF implementation.

## For Security Architecture

The [Execution Integrity Model](docs/execution-integrity-model.md) applies the same thinking to a
system review. For each obligation, it asks who controls all the behavior that can fulfill or
violate it. An owner must have that control and be established as the authority accountable for
the obligation. Only that owner can issue its guarantee, under the stated assumptions and limits.
Where ownership cannot be established, the analysis records a gap.

The paper works through a Kubernetes audit path. Creating an event, exporting it, indexing it, and
retaining it are separate responsibilities. An application operator needs to know which service
controls each one and what its acknowledgement establishes. In batch-mode webhook export, a
buffer can lose an event after the API operation has committed. The analysis makes that loss
window explicit.

An operator can check whether a retained record is still retrievable, but that check does not
control the storage service's future behavior. It provides assurance about an obligation the
operator does not own: justified confidence supported by evidence. Delegating a task can leave
ownership where it was if the owner's mechanism still covers every decisive outcome. Ownership
moves when complete decisive authority transfers.

The [introduction](docs/introduction.md#ownership-and-assurance) explains how delegated work differs
from a transfer of ownership, and why the distinction matters when a system relies on an outside
service.

## What the Evidence Shows

Five case studies reconstruct systems using only parts already in the catalog. They cover a
fixed-grid differential-privacy accountant, nested CI/CD, optimistic transactional memory,
preemptive earliest-deadline-first scheduling, and a state-based replicated JSON object.

Ten dynamic-programming algorithms also use one executable Memoization composition. Each is
compared with a separately written reference on named cases and 1,000 deterministic generated
cases. Controls bypass one shared structure at a time while leaving the calculation intact;
the recipe check must reject the broken construction. This tests whether the shared parts govern
the work as well as whether the answer is correct. The
[examples directory](formal/examples/README.md) records each result and its limits.

The catalog's contracts have TLA+ specifications, machine-checked TLAPS proofs, and Verus-proved
Rust implementations. Twenty-three refinement packages relate the implementation contracts to
their specifications. Negative controls deliberately break a named property and must fail while
an isolated baseline passes.

The [supplementary research](supplementary-research/README.md) keeps failed experiments and negative
results, including checks later found not to test what they claimed. These are part of the research
record. The catalog covers the systems examined and remains open to counterexamples.

## Start Here

- Use the [`automation-structures` quick start](https://github.com/brian-c-moore/automation-structures#quick-start)
  for Rust code and the [reference](docs/reference.md) to choose structures by responsibility.
- Follow the [shared rendering/routing construction](formal/examples/README.md#shared-composition)
  to see the parts used in two domains.
- Read the [introduction](docs/introduction.md) for the relationship between the catalog, library,
  and kernel, plus the motivation and full document index.
- Check the [implementation roadmap](ROADMAP.md#implementation-and-further-research) for the
  `alk-core` target and remaining work.
- Read [Automation Structures](docs/automation-structures.md) for the theory and construction
  procedure. Use the [reference](docs/reference.md) to look up individual structures.
- Follow [ALK Claims](docs/alk-claims.md) for a worked example of the Automation-Layer Kernel (ALK).
  The ALK combines selected contracts into one governed execution plan; the guide connects those
  contracts to control over actions and the claims the system can issue.

## Verify the Work

The [formal methods directory](docs/formal-methods.md) links claims to their models, proofs, and
controls. The [reproducibility guide](docs/reproducibility.md) gives the pinned Docker build and run
commands, including how to select one subject such as Budget. Each result applies to its written
property and assumptions; a model check covers its configured state space.

## Repository and Status

This is experimental, open research. The repository contains the theory, formal artifacts,
examples, and verifier. The Rust structures are published separately as
[`automation-structures`](https://crates.io/crates/automation-structures), with source on
[GitHub](https://github.com/brian-c-moore/automation-structures).

`alk-core` is the Automation-Layer Kernel (ALK) implementation under development. Its intended
public model is components and flows, with native streaming and one governed execution plan.
Full kernel integration and implementation conformance remain open. The [roadmap](ROADMAP.md)
separates existing results from the remaining implementation and research work.

This project began as an experiment in AI-human collaboration in January 2025. The
[project history](docs/introduction.md#the-meta-experiment) describes how it developed, and the
[AI Use and Ethics Policy](docs/ai-use.md) explains how I use AI and where I draw the line.

## Contributing

If you discover something that cannot be built using the structures in the catalog, I would like
to hear from you. Questions about an unclear definition, a confusing example, or where a
construction got stuck are welcome too. [CONTRIBUTING.md](CONTRIBUTING.md) explains how to raise an
issue or propose a change.

## License

Unless otherwise noted, the original work in this repository is released under the
[MIT License](LICENSE). Third-party tools and test data retain their respective licenses, listed
in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
