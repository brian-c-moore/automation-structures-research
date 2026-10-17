# Frequently Asked Questions

Automation Structures collects reusable ways to govern behavior: keeping resource use within a
budget, selecting among competing candidates, advancing work, and preserving evidence. This page
answers common questions about what the structures are, how to build with them, and how to read
the research's claims.

Start with [data structures](#are-these-data-structures),
[a concrete example](#can-you-show-me-a-simple-example),
[composition](#if-the-parts-are-verified-is-their-composition-automatically-correct),
[formal evidence](#what-has-actually-been-formally-verified), or
[getting started](#how-should-i-start).

## Are these data structures?

Some have familiar data structures inside them. A ResourceRegistry maintains a key-to-value
mapping, a QualityHierarchy organizes representations in a tree, and a Budget keeps accounting
state. They also define the permitted operations and the responsibilities those operations must
preserve.

For example, a map can store allocation records. A Budget contract says how allocations,
reservations, and pending evictions must be accounted for so that admitted use stays within
capacity. The representation is one implementation choice; the capacity obligation is what makes
Budget a reusable automation structure.

Abstract data types are a useful comparison because they describe values through operations and
their contracts. The catalog also includes execution and coordination behavior, such as joining
parallel work and governing iteration. See [State and Behavior](introduction.md#state-and-behavior).

## Aren't these just state machines?

They are state-machine abstractions. Each describes relevant state, initial conditions, and
permitted transitions. Here, that can mean counters, collections, and relations; it need not mean
a small diagram of named states such as `Idle`, `Running`, and `Done`.

The research asks which state-machine abstractions make useful reusable parts. An entry needs a
recognizable responsibility, an explicit contract, and evidence about how it behaves and composes.
Giving arbitrary code a state-machine description does not by itself establish those things.

## What do you mean by an "obligation" and a "contract"?

An obligation is a responsibility the system accepts for its behavior. "Admitted use stays within
capacity" is one. "Accepted work eventually finishes" is another. A deployment pipeline can have
such responsibilities even if nobody has written them down.

A contract expresses the properties used to assess that responsibility, together with the
assumptions under which they hold. For example, progress may depend on a scheduler eventually
running eligible work. An *obligation schema* is the reusable form; applying it to a particular
resource, scope, and failure model creates a concrete obligation.

One obligation can require several formulas. Facts about types and counters may support its
proof without becoming additional promises. The [reference](reference.md#common-semantic-record)
separates those roles.

## Can you show me a simple example?

Suppose a system has capacity for ten units of a resource. Six are allocated, two are reserved,
and one is awaiting eviction. The Budget contract counts all three:

```text
allocated + reserved + pending_eviction <= capacity
    6     +    2     +        1         <=    10
```

Only one unit remains available. A reservation already commits capacity. Asking for an eviction
does not free the pending unit; completing the eviction does.

Now suppose two callers each check that one unit remains, then each allocate it. Both checks can
pass while their combined allocation violates the bound. The construction must keep the check
valid through the allocation's commit, using a mechanism that covers every relevant allocation
path. A counter and a successful check alone do not supply that enforcement.

The same accounting contract can govern bytes, operations, or another counted resource. Each
system still has to connect the accounting to the resource use it claims to control. See the
[Budget model](../formal/structures/Budget/Budget.tla) and
[formal evidence directory](formal-methods.md#retained-structures).

## How is this different from design patterns or contract-based design?

There is substantial overlap. Design patterns name recurring solutions. Abstract data types
describe operations and their contracts. Component and contract-based methods examine what
assemblies preserve and what their environments must supply.

Automation Structures brings those concerns together around a catalog of reusable behavioral
responsibilities. Its construction method asks which parts supply each responsibility, what
happens where they connect, how work advances, and which authority controls fulfillment. The
catalog connects those questions to specifications, implementations, examples, and checks.

The intended contribution is a useful synthesis and construction method. The research does not
claim that contracts, state machines, or compositional reasoning originated here. The
[related-work discussion](introduction.md#relationship-to-prior-art) explains the connections.

## Does "automation" mean workflows, AI agents, or concurrent systems?

The term is broader here. Automation begins when a built system executes work under an obligation
without a human enforcing each step. That includes ordinary sequential programs as well as
workflows, parallel computations, and streams. A person can still approve an action or start a run.

A trigger and an execution structure answer different questions. A timer, message, API request,
or human action can start the same kind of computation. AI can supply part of the domain work,
but AI is not required by the theory. See the
[working definition](automation-structures.md#23-a-working-definition-of-automation).

## Why these structures? Is the catalog complete or minimal?

The catalog came from comparing systems across twelve surveyed domains, then testing proposed
constructions and challenging them with further examples and algorithm corpora. Recurrence made
a candidate worth investigating; admission also required a reusable responsibility and evidence
for its claimed role.

The current [reference](reference.md) has 23 entries: nine abstraction primitives, ten named
compositions, and four execution structures. "Primitive" is relative to the chosen abstraction
and allowed connective forms. It means the obligation-bearing behavior is not supplied by a
validated reduction to the other entries on that basis.

This is not a proof of a universally complete or uniquely minimal catalog. A faithful reduction
can reclassify a primitive as a named composition. Signal and RateLimit retain useful names even
though the research records how to construct them from other parts.

## Why stop here instead of reducing everything to functions, loops, and counters?

The stopping point is meant to preserve useful responsibilities. Reducing a Budget to arithmetic
can explain how its counters change while losing the fact that some part must prevent excess
admission. A builder still needs to know where that responsibility lives.

The catalog explicitly allows connective forms such as Cursor, Buffer, and Accumulator. They
carry position, pending work, or partial results under another contract. If a particular buffer
is also supposed to guarantee bounded capacity or delivery, the construction must identify the
contract that supplies that additional responsibility.

This boundary keeps a reduction from hiding the original obligation in its glue. See
[connective forms](reference.md#connective-forms) and the
[Turing Tarpit question](domain-abstraction-collapse.md#16-the-turing-tarpit-question).

## Does removing domain vocabulary throw away the important details?

Domain Abstraction Collapse replaces local names with structural roles while retaining the
behavior and responsibilities under examination. Reconstruction then checks whether the proposed
parts can recover them. Anything the mapping cannot explain stays visible as a residual.

The domain still supplies content such as scoring rules, physical equations, recurrence relations,
and effects. Recognizing selection in two systems does not make their scoring functions
interchangeable. A mapping is useful only to the extent that it preserves the claimed behavior
and responsibilities. The [DAC method](domain-abstraction-collapse.md#12-the-methodology-domain-abstraction-collapse)
spells out that process.

## Is there a concrete example of reuse across domains?

Yes. Rendering level-of-detail selection and route selection invoke the same executable
`rooted_frontier` composition. It organizes candidates, traverses them, selects a result, and
records a snapshot using QualityHierarchy, TraversalEngine, CompetitiveSelection, and
AllocationSnapshot.

Rendering supplies quality and resource-cost policies to select a frontier within a byte budget.
Routing supplies path costs and selects minimum-cost alternatives for each target, retaining
ties. The route example has no route-slot budget.

The [shared-composition example](../formal/examples/README.md#shared-composition) describes the
implementation and controls. Its scope is these selection problems; it does not implement a full
renderer or the OSPF protocol. A second example is the
[Memoization family](../formal/examples/README.md#memoization-family), where ten algorithms use
one composition with different recurrences and reduction operations.

## How much domain code is still needed? Could arbitrary code hide the real work?

Domain code remains necessary. A structure can govern which candidate is selected without
inventing a useful score, or govern an effect without supplying the application's effect logic.
The amount of domain code depends on the problem.

There is also a real test here: a reconstruction must identify the role of every part supporting
its claim. If an allegedly ordinary callback independently enforces capacity, delivery, or another
claimed reusable obligation, that responsibility needs an explicit account. Calling it a
parameter does not establish that the catalog supplied it.

The executable examples separate output agreement from structural construction checks. Some
controls bypass a shared structure while keeping the numerical result correct. Those runs must
fail the recipe check. See [the examples' evidence rules](../formal/examples/README.md).

## If the parts are verified, is their composition automatically correct?

No. A component's proof depends on its assumptions, and another component can invalidate them.
Their connection can also introduce a responsibility neither part supplies on its own.

Suppose selection chooses the highest-scoring candidate and actuation later applies an effect to
it. If scores change between those operations, the selected candidate may be stale. The
[SelectThenActuate model](../formal/composition/structure-compositions/SelectThenActuate.tla)
invalidates a pending selection when scores change, so another selection is needed before
actuation.

A composition argument must cover shared state, relevant transitions, assumptions, and the
conditions at the connection. The retained composition theorems establish their stated
combinations under their premises. They do not authorize arbitrary wiring of verified parts.

## Why distinguish execution structures from the shape of the work?

Dependencies describe which work relies on which other work. Execution describes how that work
starts, makes visible progress, exchanges results, and completes.

| Execution structure | What advances or completes |
|---|---|
| Sequential | One logical work locus advances in a declared order |
| Fork-join | Sibling work runs and resolves under an explicit join rule |
| Step graph | Predecessor completion enables later steps |
| Stream graph | Records move between stages while upstream work can remain active |

A graph of operators can finish whole stages before releasing results, or pass records between
active stages. Those choices create different progress and flow-control obligations. A cyclic
input graph also need not imply cyclic execution; visiting its nodes can be a finite computation.

The four structures can be combined at different boundaries. Their refinement results depend on
the stated mappings and observations; they do not rank implementations by speed. See
[Execution Structures](execution-structures.md).

## Does preventing bad outcomes also guarantee that work finishes?

No. A system that admits no work might never exceed its budget, yet be useless to its callers.
Safety concerns forbidden outcomes. Liveness concerns required progress.

Progress needs its own argument and assumptions, such as eventual scheduling, delivery, or a
decreasing measure that prevents endless iteration. A retry loop can preserve a safety invariant
while running forever. The research therefore records
[safety and liveness separately](execution-structures.md#75-safety-and-liveness-remain-separate).

## What does "ownership" mean here? Is it Rust ownership?

Ownership here means technical enforcement ownership of a particular obligation. A complete claim
frame fixes what is promised, for which subject, at which boundary, and under which observations
and failures. One eligible authority or named protocol is established as the canonical owner
because it covers all behavior decisive for that obligation. Otherwise, an ownership gap remains.

Rust's ownership rules can contribute to an implementation's enforcement, but they do not by
themselves establish this broader relationship. Nor does storing a resource identifier establish
control over the resource. Technical accountability belongs to the canonical owner at the same
claim frame.

Creating an audit event and retaining it for a year are different obligations, potentially with
different owners. The [ownership paper](claim-relative-ownership.md) defines the full frame and
the conditions for ownership.

## Does one owner mean everything must be centralized? What about delegation?

A single canonical owner at one claim frame can be a named distributed protocol whose combined
authority covers the obligation. Its participants can own distinct responsibilities at more
specific frames. Naming a collection of services is insufficient; the protocol must account for
the decisive behavior and its failure conditions.

Delegating work creates a trust boundary. Ownership stays with the owner while its mechanism
still covers every decisive outcome. Transferring complete decisive authority moves ownership
and technical accountability. Splitting that authority without an owning protocol leaves the
end-to-end obligation unowned, even when each participant can guarantee something narrower.

See [accountability, delegation, and transfer](claim-relative-ownership.md#4-accountability-delegation-and-transfer).

## What is the difference between a guarantee and assurance?

A mathematical contract guarantee is a consequence under stated assumptions. An owner-issued
guarantee is a claim from the authority that owns a concrete obligation. A proof alone does not
establish an owner or give a deployment that authority.

Assurance is justified confidence in an outcome controlled elsewhere, supported by identified
evidence and assumptions. An application can guarantee that it checks a storage acknowledgement
before proceeding. That acknowledgement provides assurance about the storage service's outcome;
it does not give the application control over the service's future retention behavior.

Assurance can be useful and strong. Its record must say which proposition the evidence supports,
who produced and checked it, when it was valid, and what could defeat it. See
[Ownership and Assurance](introduction.md#ownership-and-assurance).

## Is checking or logging an action enough to enforce its contract?

A check supports an action only while the checked condition remains valid through the decisive
commit. Every path that could violate the claimed property has to be covered. A later log entry
can help detect a violation without preventing it.

Evidence also has responsibilities of its own. A hash chain can reveal certain alterations under
its hash and anchor assumptions; it does not by itself establish that every required event was
recorded or will remain available. A signed receipt can bind an origin without proving continued
truth or durability.

The [Execution Integrity Model](execution-integrity-model.md) distinguishes prevention, detection,
recovery, and evidence custody so that each claim matches the mechanism supporting it.

## What has actually been formally verified?

The research provides several kinds of evidence, with different meanings:

| Evidence | What it establishes |
|---|---|
| TLC model check | A named property holds throughout the configured finite state space |
| TLAPS proof | A written theorem follows from its definitions and assumptions |
| Verus implementation proof | The selected Rust implementation satisfies its written Verus contract |
| Refinement evidence | The named state and action mappings preserve the specified behavior or observations within their scope |
| Negative control | A check detects the particular defect deliberately introduced |
| Executable example | The registered construction and output checks pass on the exercised cases |

Each catalog entry has a formal evidence chain for its written clauses and a named
implementation-refinement package. There are also results about particular compositions,
execution refinements, ownership relationships, and selected ALK constructions. These are
separate claims with separate premises.

The [formal methods directory](formal-methods.md) is the place to check a specific claim. A theorem
about a model, a Rust contract proof, and an example returning the right answer each answer a
different question. None establishes that every application built from the catalog is correct.

## Are the proofs all limited to tiny examples?

Finite model checks have explicit bounds. They explore all modeled behaviors inside those
bounds, including interleavings that ordinary tests may miss. Theorem proofs can quantify beyond
a particular finite configuration when their statements do so.

For example, the selected Budget/Sequential integration uses capacity two and two steps, while
the Budget safety theorem applies to any natural-number capacity. The broader Budget theorem
does not enlarge the separate integration result. The
[ALK Claims guide](alk-claims.md) records that distinction.

For any result, check the exact property, parameters, assumptions, and observations. Small models
can expose decisive counterexamples; their success does not settle behavior outside their scope.

## Does formal verification make a system secure, production-ready, or faster?

Those conclusions need additional evidence. A proof addresses its specification. A real system
also has domain logic, external dependencies, deployment authority, failure behavior, and an
implementation that must preserve the relevant specification. Choosing the right obligation is
itself part of the work.

Performance depends on the implementation and workload. Representation choices, coordination,
evidence retention, and domain operations all have costs. Structural reuse can provide shared
implementation and proof work, but neither a catalog classification nor a formal proof establishes
a speedup or lower development cost.

The [roadmap](../ROADMAP.md#implementation-and-further-research) identifies implementation
conformance, reuse through the engine, and performance measurement as separate workstreams.

## How do the research, the Rust library, and the ALK relate?

| Project or term | Role |
|---|---|
| Automation Structures Research | Defines the catalog, construction method, contracts, examples, and formal evidence |
| `automation-structures` | Supplies reusable Rust implementations under documented executable profiles |
| Automation-Layer Kernel (ALK) | A construction that brings selected contracts into one governed execution plan and accounts for authority and evidence |
| `alk-core` | The kernel implementation being built by composing the reusable structures |

The research's ALK model, conditional theorem, worked profiles, and selected claim integration
provide evidence for their stated boundaries. They do not certify the whole kernel implementation.
Full kernel integration and implementation conformance remain open in the
[research roadmap](../ROADMAP.md).

## Do I need Rust, an ALK, or formal-methods expertise to use the ideas?

You can use the method to analyze an existing system or plan a new one in any language. The
immediate exercise is to state a responsibility, locate the behavior that decides it, and examine
what the proposed parts and their connections preserve.

The Rust library is one implementation route. An ALK is a construction for bringing selected
contracts under a governed execution authority; it is not a prerequisite for recognizing or using
an individual structure. A different implementation needs evidence appropriate to its own claims.

Reading the examples does not require running the proof tools. Evaluating or extending a formal
claim does require understanding its specification and assumptions. The
[reproducibility guide](reproducibility.md) explains how to inspect and run focused checks.

## What would show that the theory or a proposed construction is wrong?

A *falsifier* is a condition or example that defeats a particular claim. An execution that
violates a stated invariant while satisfying its assumptions would refute that invariant claim.
A purported cross-domain reconstruction that loses required behavior would refute its mapping.

A *residual* is something the proposed account has not explained or supplied. It might reveal a
missing structure, an unsuitable composition, unsupported domain behavior, or an implementation
gap. It is a finding to investigate. It cannot silently receive credit from the rest of the recipe.

A successful reduction of a primitive can revise its classification without invalidating its
usefulness. The [claims and limits](automation-structures.md#10-claims-and-limits) state what would
challenge each kind of result. [Contributing](../CONTRIBUTING.md) also welcomes unclear explanations
and attempted constructions that get stuck; a finished counterexample is not required.

## Was AI used to produce this research?

Yes, extensively and deliberately. The project began as an experiment in AI-human collaboration.
The [AI Use and Ethics Policy](ai-use.md) describes the author's direction, judgment, review, and
accountability, and distinguishes personal communication, collaborative technical writing, and
technical artifacts.

The policy's central distinction is authenticity and accountability rather than manual authorship
of every line. AI-generated specifications and proofs still need review: machine checking can
establish a written result without establishing that the specification asks the right question.

## How should I start?

Choose one responsibility in a system you understand, such as keeping admitted use within a
capacity limit. Write down what must hold, how it could fail, and who can cause or prevent that
failure before selecting a structure.

Then use the [reference](reference.md) to find a candidate contract and the
[shared rendering/routing example](../formal/examples/README.md#shared-composition) to see how
parts are assembled. The [six-step construction procedure](automation-structures.md#81-the-design-procedure)
guides the rest: classify the work, select execution, instantiate obligations, map ownership and
assurance, and check the design and implementation.

For a specific claim, follow the [formal methods directory](formal-methods.md) to its evidence and
the [reproducibility guide](reproducibility.md) to a focused check. Record what remains unresolved;
those questions are useful inputs to the research.
