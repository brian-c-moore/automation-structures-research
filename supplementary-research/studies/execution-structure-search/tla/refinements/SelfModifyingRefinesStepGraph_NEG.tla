---- MODULE SelfModifyingRefinesStepGraph_NEG ----
\* ====================================================================
\* NEGATIVE CONTROL for the self-modification claim.
\*
\* The defused mechanism is one: the dependency-axis guard on AddDependency is
\* removed, so a node may acquire a new prerequisite AFTER it has already begun
\* or finished executing. Two further differences from
\* SelfModifyingRefinesStepGraph, stated rather than left to be found: the target
\* is no longer un-readied when it acquires a prerequisite, and two of that
\* module's five invariant definitions are absent here --
\* MutationOnlyBeforeEligibility and ExecutionRespectsCurrentGraph -- so this
\* module defines the three its own config checks.
\*
\* The control makes the positive result falsifiable. Without it, "the
\* step-graph discipline survives self-modification" could hold because the
\* model cannot express the hazard. Here the model can express it, and TLC
\* finds it: a node completes, then a dependency is added pointing at it from a
\* node that never ran, and NoRunBeforePredecessors is violated retroactively.
\*
\* Expected: VIOLATION of NoRunBeforePredecessors.
\*
\* The result this pair establishes: self-modification is a dependency-axis
\* variant rather than a modality variant, and only under a dependency policy
\* that forbids retroactive dependency addition. Without such a policy the
\* discipline fails, and the failure is not a new modality either -- it is an
\* unsound dependency policy, on the same axis.
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

Init ==
    /\ edges  = {}
    /\ nstate = [n \in Nodes |-> "Ready"]

\* THE ONE DIFFERENCE. The guard
\*     nstate[n] = "NotReady" \/ nstate[n] = "Ready"
\*     nstate[n] # "Running"
\*     nstate[n] # "Completed"
\* is GONE, and the target is no longer un-readied. A dependency may now be added
\* to a node that is already Running or Completed -- deciding an eligibility
\* question that was already decided, with a different answer.
AddDependency(p, n) ==
    /\ p # n
    /\ <<p, n>> \notin edges
    /\ edges' = edges \cup {<<p, n>>}
    /\ UNCHANGED nstate

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

NoRunBeforePredecessors ==
    \A n \in Nodes :
        (nstate[n] = "Running" \/ nstate[n] = "Completed") =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"

ValidStates == \A n \in Nodes : nstate[n] \in NodeStates

ThreeNodes  == {1, 2, 3}
FourStates  == {"NotReady", "Ready", "Running", "Completed"}
====
