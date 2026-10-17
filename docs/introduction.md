# Introduction to Automation Structures

Automation Structures Research provides a catalog of reusable state-machine abstractions,
organized around behavioral obligations, with explicit contracts and conditions for composition.
The practical result is a set of parts to build with. The theory explains why these abstractions
were selected, how their contracts can be preserved, and what can fail when they are assembled.

The projects provide successive parts of that construction:

| Project | What it provides |
|---|---|
| Automation Structures Research | A catalog of reusable state-machine abstractions, organized around behavioral obligations, with explicit contracts and conditions for composition. |
| `automation-structures` | A Rust library of reusable state-machine implementations, organized around behavioral obligations, with explicit contracts and conditions for composition. |
| `alk-core` | An automation kernel under development, composed of those reusable state-machine implementations, organized around behavioral obligations, with explicit contracts and conditions for composition. |

Start with the [Rust library](https://github.com/brian-c-moore/automation-structures) to use the
implemented structures, or the [shared rendering/routing construction](../formal/examples/README.md#shared-composition)
to see one assembly used in two domains. The [README](../README.md) introduces the project; this
introduction explains the distinctions behind the parts and how the research developed.

## State and Behavior

A state-machine abstraction describes relevant state, possible initial values, and permitted
transitions. Budget's state includes capacity and the allocation, reservation, and pending-eviction
ledgers. Its actions change those values under stated conditions. This uses the
[general meaning of state machine](https://lamport.azurewebsites.net/tla/high-level-view.html),
which does not require a finite list of named control states.

The obligation boundary is crossed when a system accepts responsibility for its behavior;
state-machine abstractions make the actions and histories that can fulfill or violate that
responsibility explicit.

The contract states the required properties of behavior and the assumptions under which they
hold. Atomicity, clock delivery, and scheduling fairness are examples of environment assumptions;
a construction must identify which ones its selected contracts require.

Catalog membership depends on a reusable responsibility at the chosen boundary. Connective
helpers such as Cursor and Buffer also have state and transitions, but their catalog role supports
another structure's obligations. An entry can offer alternative modes or carry several distinct
obligations. A catalog name therefore need not identify exactly one state machine or one obligation.

## Reusable Responsibilities

A CPU budget and a spending budget apply the same rule to different resources: admitted use must
stay within capacity. The reusable rule is an obligation schema. Applying it to a particular
system creates an obligation with a subject, scope, and failure model. The rule alone does not
specify how either system enforces it. A CPU scheduler and an account ledger need different
mechanisms even when their accounting follows the same capacity rule.

The Budget contract accounts for allocated, reserved, and pending-eviction charges together. A
reservation already commits capacity. Moving an allocation into pending eviction does not make
that capacity available again; the charge stays until eviction completes. Transfers between the
ledgers must preserve the total.

The obligation is the responsibility accepted for the system's behavior. Its mathematical
contract expresses conditions used to assess fulfillment. A construction must identify the
mechanism that controls the decisive behavior and its accountable owner, or record an ownership
gap. A mathematical specification and its proof do not establish that authority.

The proof needs facts about the counters and assumptions about permitted writes. Those supporting
facts help prove the capacity contract; they do not become separate responsibilities.

Other structures govern different behavior. A ResourceRegistry maintains a key-to-value mapping.
An AuditSink preserves a chain of mutation records under its hash and anchor assumptions. The
[reference](reference.md) gives the contracts and current catalog: nine abstraction primitives,
ten named compositions, and four execution structures. Seven connective forms join or organize
the parts without adding independent obligations.

A useful analogy for where Automation Structures sits in relation to prior art is the CAGED
system for composing music on a guitar. The CAGED system identifies chord "shapes" on a guitar
neck that can be moved around in various ways to make music. It isn't competing with music theory
or claiming any other system of making music is somehow incorrect. It operates at a different
abstraction layer from those other systems. The shapes stay the same while the notes change, the
same way an automation structure keeps its form while the domain supplies the content.

## Assembling a System

The construction method starts with the problem. State what the system must do and which failures
it must withstand, then select structures with contracts that address those responsibilities.
Where the structures connect, check whether they preserve each other's obligations and supply
what the other needs. A successful component proof alone cannot settle that question.

Select the primitive and named-composition contracts that govern the work, then select the
execution contracts that govern how it advances. These are separate selection axes. Using Budget
for capacity control, for example, leaves the choice of Sequential or StepGraph execution open.

Work shape and execution structure are separate choices. Dependencies between steps may be
linear, branching, reconvergent, or cyclic. A runtime may advance them one at a time, across
workers that meet at a barrier, as a graph of ready steps, or as a stream. Knowing the dependencies
does not settle how the work should run. [Execution Structures](execution-structures.md) develops
those choices and the conditions under which they can be combined.

The rendering/routing example tests reuse through one executable construction. Other examples
test the catalog by reconstructing existing systems or comparing results with separately written
references. The [examples directory](../formal/examples/README.md) states what each test covers.
An unexplained part of a reconstruction is a residual to investigate, and may require a change to
the catalog.

## Ownership and Assurance

I was intrigued by cloud security's treatment of data ownership, accountability, custody, and
delegation. Pushing that idea down through smaller abstraction layers exposed a more general
question: which authority controls the behavior that can decide whether this obligation is met,
from this perspective?

The same question works when the subject is an organization, a whole system, a component,
a protocol, or one algorithmic transition. The obligation and the authority both need to be
stated at the level being examined.

The perspective must be precise. Creating an audit event and retaining it for a year are
different obligations, even when they concern the same record. The claim frame fixes the promise
being evaluated, the system boundary, and the conditions of the claim.
[Claim-Relative Ownership and Assurance](claim-relative-ownership.md) defines the complete frame.

At one complete claim frame, an obligation has exactly one canonical owner or none. The owner
must control the behavior that can determine whether the obligation is fulfilled, and be
designated to answer for it. No owner can mean either that control is missing or that an eligible
authority has not been established as the owner. Those gaps need different repairs.

Accountability is intrinsic to ownership. Only that owner can issue the obligation's guarantee
under the stated assumptions and limits. Different abstractions can own related obligations;
they do not share ownership of one unchanged obligation.

Handing off work does not by itself hand off ownership. If the owner's mechanism still covers
every decisive outcome, the owner remains accountable. Transferring complete decisive authority
moves ownership and technical accountability with it. Splitting that authority without one owning
protocol leaves the end-to-end obligation unowned. This is the Law of Non-Delegable Enforcement
developed in the [Execution Integrity Model](execution-integrity-model.md).

A former owner's claim about the transferred obligation becomes assurance: justified confidence
in an external outcome, supported by named evidence. The former owner can still own local
obligations such as checking a response or requesting recovery. The Kubernetes audit example in
the EIM paper works through these distinctions for event creation, export, indexing, and retention.

## The Automation-Layer Kernel

The Automation-Layer Kernel (ALK) applies the construction method to an execution system. It
selects contracts, adds the obligations created at their connections, and produces one governed
execution plan that can be checked before it runs. Its ownership extends only to obligations
whose decisive behavior it controls. Claims about externally owned obligations require assurance.

The [ALK Claims guide](alk-claims.md) follows a selected Budget/Sequential construction. It connects
two obligation schemas to the structures' predicates and actions, then checks the authority and
evidence needed to issue claims. The wider construction registry relates 36 schemas to 69 clause
occurrences across the 23 catalog entries. These counts distinguish responsibilities from the
supporting formulas and alternative modes used to express them; they are not counts of independent
guarantees.

The repository also contains construction proof kernels under `formal/construction/kernels/`.
They establish reusable results about assembly, progress, refinement, and ownership under their
premises. The ALK work under `formal/construction/alk/` uses selected contracts to describe a
system's execution. The [formal methods directory](formal-methods.md) identifies both sets of
artifacts and their limits.

`alk-core` is the implementation target, built by composing the separately published
[`automation-structures`](https://crates.io/crates/automation-structures) library. The intended
kernel brings the catalog's structures together as the common building blocks for its own
execution machinery and the components developers assemble into flows. Each flow selects the
contracts it needs. Reusable component hierarchies lower into one admitted plan under one kernel
execution authority.

The research supplies contracts and worked claim integrations. `alk-core` is still under
development; full catalog integration and whole-kernel conformance have not been established.
Its execution must satisfy the selected contracts and enforce the declared authority. The
[roadmap](../ROADMAP.md) records the remaining work.

## Relationship to Prior Art

Others have described related boundaries while working on different problems. Martin Kleppmann's
[convergence survey](https://queue.acm.org/detail.cfm?id=3546931) shows where convergent replication
stops being enough. A limited resource, such as an account that must not be overdrawn or a seat that
must not be sold twice, forces coordination. Those examples match Budget and CompetitiveSelection
in this catalog.

Ink & Switch's
[Convergence Is Not Enough](https://www.inkandswitch.com/livelymerge/notebook/lm-02/) distinguishes
replaying previously computed writes from reapplying the intended operations. It also shows why
invariants across objects need composition rules: convergent parts can still form an invalid list
or tree. The authors propose abstract-type operations with defined merge semantics, discuss
replay and rejection strategies, and note that accepted work may later be rolled back. General
support for user-defined types remains unresolved.

For Automation Structures, the relevant connection is how a reusable contract binds to permitted
operations, survives composition, and states what acceptance guarantees over time. This is also
why a construction must account for relationships between its parts and the behavior at their
connections.

My aim is a useful synthesis of ideas about obligations, composition, execution, and authority.
Related work provides ways to compare and challenge the account. For example,
[BIP](https://www-verimag.imag.fr/~iosif/ProgramVerificationHomepage/quinton-branch/bip.php)
describes components through behavior, interaction, and priority; coordination is part of the
construction. Benveniste, Caillaud, and Passerone's
[contract model](https://arxiv.org/abs/0706.1456) formalizes component composition across multiple
aspects of a system. The
[STPA handbook](https://psas.scripts.mit.edu/home/books-and-handbooks/) explains how to examine
control structures, unsafe control actions, and loss scenarios.

These connections suggest useful questions here: what does an assembly preserve, which authority
controls its decisive behavior, and have I stated the right obligation in the first place?
Automation Structures organizes its own catalog and construction method around those questions.

The [Automation Structures paper](automation-structures.md) develops the construction method and
its evidence. [Domain Abstraction Collapse](domain-abstraction-collapse.md) describes how the
catalog was found and relates the method to earlier work.

## The Meta Experiment

This research began as an experiment in AI-Human collaboration in January 2025. I wanted to use AI
as an assistant to build the automation platform that I wanted to have as a practitioner. I started
with some inspirations and intuitions, then used AI to build prototypes to explore and refine ideas.
After the fifth or sixth prototype, I started seeing the patterns I wanted to build around and where
the abstractions started to fit my mental model. I had lots of questions still and this research is
my attempt to answer them.

This research is also the mental model I use to analyze the security architecture of a system.
Threat-modeling frameworks like STRIDE and PASTA have always felt ambiguous to me. I built this for
myself, to understand how systems work well enough to personally reason about them, and that was
part of the question I was searching for an answer to. The Execution Integrity Model came out of
that search. Once the structures and their obligations have names, the next questions are which
authority owns each obligation, which actions, omissions, and trace behaviors decide it, and what
kinds of failure each guarantee or assurance can survive.

The [AI Use and Ethics Policy](ai-use.md) explains how I use AI in the project and where I draw the
line.

## Document Index

| Document | What it helps you do |
|---|---|
| [Frequently Asked Questions](faq.md) | Resolve common questions about the structures, construction method, and evidence |
| [Automation Structures](automation-structures.md) | Follow the theory and use its construction procedure |
| [Automation Structures Reference](reference.md) | Look up structures, connections, and execution modes |
| [Domain Abstraction Collapse](domain-abstraction-collapse.md) | Compare systems after removing domain vocabulary |
| [Execution Structures](execution-structures.md) | Choose how work advances and check how execution structures combine |
| [The Execution Integrity Model](execution-integrity-model.md) | Trace control and assurance through a system's architecture |
| [Claim-Relative Ownership and Assurance](claim-relative-ownership.md) | State a complete claim and establish its owner |
| [ALK Claims](alk-claims.md) | Follow a worked contract binding and the reference-state certificate |
| [Formal Examples](../formal/examples/README.md) | Inspect executable constructions and their checks |
| [Formal Methods Directory](formal-methods.md) | Find the formal artifacts for a claim and understand their limits |
| [Reproducibility Guide](reproducibility.md) | Build the verifier, select checks, and interpret results |
| [LeanFormer Case Study](leanformer.md) | Read an early construction experiment outside my background |
| [Research Record](research.md) | Locate studies that informed the catalog |
| [Supplementary Research](../supplementary-research/README.md) | Inspect failed experiments, negative results, and candidate searches |
| [Roadmap](../ROADMAP.md) | See what exists and what is planned next |
| [AI Use and Ethics](ai-use.md) | Understand how I use AI and where I draw the line |
