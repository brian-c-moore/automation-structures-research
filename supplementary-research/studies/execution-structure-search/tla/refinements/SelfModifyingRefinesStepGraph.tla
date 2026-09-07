---- MODULE SelfModifyingRefinesStepGraph ----
\* ====================================================================
\* Runtime self-modification of an execution graph, formalized.
\*
\* Agent frameworks construct or modify their own execution graphs at runtime
\* in response to model outputs. The question formalized here is whether
\* self-modification is a dependency-axis variant rather than a modality
\* variant.
\*
\* The test for modality distinctness is asymmetric simulation: two models
\* mutually simulable in their native primitives are the same way to execute.
\* So "not a modality variant" is the claim that a self-modifying graph is
\* still doing STEP-GRAPH execution -- that the step-graph defining discipline
\* survives runtime mutation of the graph. And "a dependency-axis variant" is
\* the claim that what makes it survive is a rule about DEPENDENCIES, not a
\* change to how work proceeds.
\*
\* Both halves are stated here, and the two are not independent checks:
\*
\*   NoRunBeforePredecessors -- StepGraph's defining discipline, stated over the
\*       CURRENT (mutable) edge relation. It holds. The modality is unchanged.
\*
\*   MutationOnlyBeforeEligibility -- the dependency-axis rule, written through
\*       Rank. Rank is injective on the four states the config binds, so as a
\*       STATE predicate this is NoRunBeforePredecessors again under a second
\*       name rather than a second condition. The dependency-axis content is
\*       carried by AddDependency's eligibility guard, which is an ACTION guard
\*       and is what the paired _NEG module removes.
\*
\* The result is conditional on that guard. Drop it and the discipline breaks:
\* SelfModifyingRefinesStepGraph_NEG removes the eligibility guard and violates
\* NoRunBeforePredecessors. Self-modification is therefore a dependency-axis
\* variant only under a dependency policy that forbids retroactive dependency
\* addition. Unrestricted self-modification is not a modality either; it is an
\* unsound dependency policy.
\*
\* Self-contained, per this tree's convention: no cross-directory EXTENDS. The
\* node set is fixed and the EDGE RELATION is the mutable state, which is what
\* modifying an execution graph means here. Growing the node set is the
\* degenerate case (an undeclared node is one with no in-edges yet run), and is
\* covered: a node with no incoming edges is Ready from the start, exactly as in
\* StepGraph.
\* ====================================================================
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, NodeStates

VARIABLES nstate, edges

vars == <<nstate, edges>>

Predecessors(n) == {p \in Nodes : <<p, n>> \in edges}

Rank(s) ==
    CASE s = "NotReady"  -> 0
      [] s = "Ready"     -> 1
      [] s = "Running"   -> 2
      [] s = "Completed" -> 3
      [] OTHER           -> -1

TypeInvariant ==
    /\ nstate \in [Nodes -> NodeStates]
    /\ edges \subseteq (Nodes \X Nodes)

\* Start from the empty dependency relation: every node is eligible, and the
\* graph is built entirely at runtime. This is the agent-loop shape.
Init ==
    /\ edges  = {}
    /\ nstate = [n \in Nodes |-> "Ready"]

\* ---- THE SELF-MODIFICATION ------------------------------------------------
\* The execution graph gains a dependency at runtime, in response to something
\* the run produced.
\*
\* THE DEPENDENCY-AXIS GUARD: the target must not yet have become eligible.
\* A node whose eligibility has already been decided cannot acquire a new
\* prerequisite -- that would be deciding the same question twice with different
\* answers. Nothing here constrains HOW work proceeds; the constraint is
\* entirely about when a dependency may be established.
AddDependency(p, n) ==
    /\ p # n
    /\ <<p, n>> \notin edges
    /\ nstate[n] = "NotReady" \/ nstate[n] = "Ready"
    /\ nstate[n] # "Running"
    /\ nstate[n] # "Completed"
    \* Acquiring a prerequisite un-readies the target: it must wait again.
    /\ nstate' = [nstate EXCEPT ![n] = "NotReady"]
    /\ edges'  = edges \cup {<<p, n>>}

\* ---- ORDINARY STEP-GRAPH EXECUTION ----------------------------------------
BecomeReady(n) ==
    /\ nstate[n] = "NotReady"
    /\ \A p \in Predecessors(n) : nstate[p] = "Completed"
    /\ nstate' = [nstate EXCEPT ![n] = "Ready"]
    /\ UNCHANGED edges

StartRunning(n) ==
    /\ nstate[n] = "Ready"
    /\ nstate' = [nstate EXCEPT ![n] = "Running"]
    /\ UNCHANGED edges

CompleteNode(n) ==
    /\ nstate[n] = "Running"
    /\ nstate' = [nstate EXCEPT ![n] = "Completed"]
    /\ UNCHANGED edges

AllCompleted == \A n \in Nodes : nstate[n] = "Completed"

DoneStuttering ==
    /\ AllCompleted
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Nodes, n \in Nodes : AddDependency(p, n)
    \/ \E n \in Nodes : BecomeReady(n) \/ StartRunning(n) \/ CompleteNode(n)
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* ---- INVARIANTS -----------------------------------------------------------

\* STEP-GRAPH'S DEFINING DISCIPLINE, over the CURRENT edge relation. That it
\* survives runtime graph mutation is the "not a modality variant" half of the
\* claim: the execution discipline is unchanged, so this is still step-graph
\* execution, not a fifth way of executing.
NoRunBeforePredecessors ==
    \A n \in Nodes :
        (nstate[n] = "Running" \/ nstate[n] = "Completed") =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"

\* THE DEPENDENCY-AXIS RULE that makes the above hold, stated as a checkable
\* property of the reachable state rather than only as an action guard: a node
\* that has begun executing has a settled dependency set, in the sense that every
\* prerequisite it has is already discharged.
MutationOnlyBeforeEligibility ==
    \A n \in Nodes :
        Rank(nstate[n]) >= Rank("Running") =>
            \A p \in Predecessors(n) : Rank(nstate[p]) = Rank("Completed")

\* Nothing executes on the strength of a dependency that is not in the graph:
\* the current graph is what is obeyed.
ExecutionRespectsCurrentGraph ==
    \A n \in Nodes :
        nstate[n] = "Ready" => \A p \in Predecessors(n) : nstate[p] = "Completed"

ValidStates == \A n \in Nodes : nstate[n] \in NodeStates

\* Concrete node set, for .cfg substitution (see StepGraph.tla on why topology
\* is bound by definition substitution rather than by value).
ThreeNodes  == {1, 2, 3}
FourStates  == {"NotReady", "Ready", "Running", "Completed"}
====
