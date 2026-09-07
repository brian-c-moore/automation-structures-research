--------------------- MODULE QualityHierarchyDecomposed ---------------------
(* Decomposition of quality hierarchy: allows level-violating insertions.
   AddChild without level check, or ChangeLevel without checking children,
   creates parent-child pairs where parent.level <= child.level.
   TLC finds HierarchyInvariant violated.

   Measured against formal/structures/QualityHierarchy/QualityHierarchy.tla
   and its .cfg, this is
   NOT a check-act split. Both actions are single atomic
   steps with a guard deleted: pc requires "idle" and sets "idle" in each, so
   it never takes a second value, there is no intermediate state, and there is
   no window for a concurrent party to act in. What the counterexample
   establishes is that the deleted guard is load-bearing -- a guard ablation,
   not a demonstration that the check cannot be separated from the act.

   The divergences from the module this names, none of them stated above:

     - canonical carries four variables and this carries three. `cost` and
       `children` are absent, so canonical's CostMonotonicity and
       ParentConsistency cannot even be stated here;
     - HierarchyInvariant is a DIFFERENT PREDICATE under the same name.
       Canonical quantifies over `children[n]`; this quantifies over
       `parent[n]`. The two coincide only if the relations are mutual
       inverses, which canonical asserts as ParentConsistency and this module
       neither states nor maintains;
     - canonical defines four invariants and its .cfg checks four; this
       defines one;
     - TWO mechanisms are defused, not one. AddChildNoCheck drops canonical
       AddChild's level guard AND its cost guard; ChangeLevelNoCheck drops the
       no-children and no-parent guards canonical SetNodeProperties carries;
     - `Nodes` is a local definition over quoted strings where canonical
       declares it a CONSTANT;
     - Init starts every level at 1 where canonical starts at 0. Reachability
       does not turn on that: it turns on AddChildNoCheck carrying no level
       guard, so it pairs two equal-level nodes immediately, where canonical's
       AddChild requires level[p] > level[c] and cannot fire from an all-equal
       Init at all.                                                          *)
EXTENDS Naturals, FiniteSets

CONSTANT MaxLevel   \* e.g. 3
CONSTANT NULL

VARIABLE level, parent, pc

vars == <<level, parent, pc>>

Nodes == {"n1", "n2", "n3"}

Init ==
    /\ level = [n \in Nodes |-> 1]     \* all start at level 1
    /\ parent = [n \in Nodes |-> NULL]  \* no parent relationships
    /\ pc = "idle"

(* Add child without checking level constraint *)
AddChildNoCheck ==
    /\ pc = "idle"
    /\ \E p \in Nodes, c \in Nodes :
        /\ p # c
        /\ parent[c] = NULL          \* c has no parent yet
        /\ parent' = [parent EXCEPT ![c] = p]
    /\ pc' = "idle"
    /\ UNCHANGED level

(* Change level without checking children *)
ChangeLevelNoCheck ==
    /\ pc = "idle"
    /\ \E n \in Nodes, lv \in 0..MaxLevel :
        /\ level' = [level EXCEPT ![n] = lv]
    /\ pc' = "idle"
    /\ UNCHANGED parent

Next ==
    \/ AddChildNoCheck
    \/ ChangeLevelNoCheck

(* Parent level must be strictly greater than child level *)
HierarchyInvariant ==
    \A n \in Nodes :
        parent[n] # NULL => level[parent[n]] > level[n]

Spec == Init /\ [][Next]_vars
=============================================================================
