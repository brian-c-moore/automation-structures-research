---- MODULE PropagationPassGraph_Proof ----
(* TLAPS safety and convergence proof for PropagationPassGraph.

   Parametric in Nodes, Edges, MaxIterations and MaxValue; nothing here
   depends on the path bound by the finite TLC configuration.
   EventualSettledOrIterationLimit additionally requires Nodes to be finite:
   per-node weak fairness on an
   infinite graph does not imply that every node has updated at one finite
   behavior position.

   Inv carries three round-structure auxiliaries that make the bound inductive:
   the iteration is charged at EndRound but affordability is checked at
   StartRound, so "a round is running only if the bound was affordable when
   it started" has to be carried across the round.                          *)
EXTENDS PropagationPassGraph, FiniteSetTheorems, TLAPS

ASSUME MaxIterationsType == MaxIterations \in Nat
ASSUME MaxValueType == MaxValue \in Nat
\* EventualSettledOrIterationLimit needs a finite graph. Without this assumption, an infinite
\* execution can update every fixed node eventually while never reaching the
\* state `updated = Nodes` at any finite position.
ASSUME NodesFinite == IsFiniteSet(Nodes)

\* Round-structure auxiliaries.
RoundBound     == round = "running" => iteration < MaxIterations
RunningChanged == round = "running" => changed = TRUE
SettledOK      == changed = FALSE => (values = snapshot /\ updated = Nodes)

Inv ==
    /\ TypeInvariant
    /\ IterationBound
    /\ RoundBound
    /\ RunningChanged
    /\ SettledOK
    /\ SnapshotLocality

(*-------------------------------------------------------------------------*)
(* Combine preserves the declared value range. Later steps use this lemma   *)
(* without unfolding the concrete relaxation rule.                         *)
(*-------------------------------------------------------------------------*)
LEMMA CombineTyped ==
  ASSUME NEW vals \in [Nodes -> 0..MaxValue], NEW n \in Nodes
  PROVE  Combine(n, vals) \in 0..MaxValue
  <1>A. CASE \E m \in InNbr(n) : vals[m] < vals[n]
    <2>1. PICK m \in InNbr(n) : vals[m] < vals[n]   BY <1>A
    <2>2. m \in Nodes                               BY DEF InNbr
    <2>3. vals[m] \in 0..MaxValue                   BY <2>2
    <2>4. vals[n] \in 0..MaxValue                   OBVIOUS
    <2>5. vals[n] - 1 \in 0..MaxValue
      BY <2>1, <2>3, <2>4, MaxValueType
    <2> QED  BY <1>A, <2>5 DEF Combine
  <1>B. CASE ~(\E m \in InNbr(n) : vals[m] < vals[n])
    <2> QED  BY <1>B DEF Combine
  <1> QED  BY <1>A, <1>B

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1> USE DEF Init
  <1>1. TypeInvariant     BY MaxIterationsType DEF TypeInvariant
  <1>2. IterationBound  BY MaxIterationsType DEF IterationBound
  <1>3. RoundBound        BY DEF RoundBound
  <1>4. RunningChanged    BY DEF RunningChanged
  <1>5. SettledOK         BY DEF SettledOK
  <1>6. SnapshotLocality       BY DEF SnapshotLocality
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, IterationBound, RoundBound,
              RunningChanged, SettledOK, SnapshotLocality

  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars

  <1>A. ASSUME StartRound PROVE Inv'
    <2> USE <1>A DEF StartRound
    <2>a. /\ round = "idle"
          /\ changed = TRUE
          /\ iteration < MaxIterations
          /\ snapshot' = values
          /\ updated' = {}
          /\ round' = "running"
          /\ values' = values
          /\ iteration' = iteration
          /\ changed' = changed
      OBVIOUS
    <2>1. TypeInvariant'      BY <2>a
    <2>2. IterationBound'   BY <2>a
    <2>3. RoundBound'         BY <2>a
    <2>4. RunningChanged'     BY <2>a
    <2>5. SettledOK'          BY <2>a
    <2>6. SnapshotLocality'        BY <2>a
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6

  <1>B. ASSUME NEW n \in Nodes, UpdateNode(n) PROVE Inv'
    <2> USE <1>B DEF UpdateNode
    <2>a. /\ round = "running"
          /\ n \notin updated
          /\ values' = [values EXCEPT ![n] = Combine(n, snapshot)]
          /\ updated' = updated \cup {n}
          /\ snapshot' = snapshot
          /\ iteration' = iteration
          /\ changed' = changed
          /\ round' = round
      OBVIOUS
    <2>c. Combine(n, snapshot) \in 0..MaxValue
      BY CombineTyped
    <2>1. TypeInvariant'      BY <2>a, <2>c
    <2>2. IterationBound'   BY <2>a
    <2>3. RoundBound'         BY <2>a
    <2>4. RunningChanged'     BY <2>a
    <2>5. SettledOK'
      \* the round is running, so changed is TRUE and the clause is vacuous.
      BY <2>a
    <2>6. SnapshotLocality'
      <3> SUFFICES ASSUME NEW t \in updated'
                   PROVE  values'[t] = Combine(t, snapshot')
        BY DEF SnapshotLocality
      <3>0. t \in Nodes   BY <2>a
      <3>1. CASE t = n
        <4>1. values'[t] = Combine(n, snapshot)   BY <2>a, <3>0, <3>1
        <4> QED  BY <4>1, <2>a, <3>1
      <3>2. CASE t /= n
        <4>1. t \in updated                       BY <2>a, <3>2
        <4>2. values'[t] = values[t]              BY <2>a, <3>0, <3>2
        <4>3. values[t] = Combine(t, snapshot)    BY <4>1
        <4> QED  BY <4>2, <4>3, <2>a
      <3> QED  BY <3>1, <3>2
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6

  <1>C. ASSUME EndRound PROVE Inv'
    <2> USE <1>C DEF EndRound
    <2>a. /\ round = "running"
          /\ updated = Nodes
          /\ changed' = (values /= snapshot)
          /\ iteration' = iteration + 1
          /\ round' = "idle"
          /\ values' = values
          /\ snapshot' = snapshot
          /\ updated' = updated
      OBVIOUS
    <2>b. iteration < MaxIterations   BY <2>a
    <2>1. TypeInvariant'      BY <2>a, MaxIterationsType
    <2>2. IterationBound'   BY <2>a, <2>b, MaxIterationsType
    <2>3. RoundBound'         BY <2>a
    <2>4. RunningChanged'     BY <2>a
    <2>5. SettledOK'          BY <2>a
    <2>6. SnapshotLocality'        BY <2>a
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6

  <1>D. ASSUME Terminate PROVE Inv'
    BY <1>D DEF Terminate, vars

  <1>E. CASE Next
    BY <1>A, <1>B, <1>C, <1>D, <1>E DEF Next
  <1> QED  BY <1>0, <1>E

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant           BY Safety, PTL DEF Inv
THEOREM IterationBoundSafety == Spec => []IterationBound
  BY Safety, PTL DEF Inv
THEOREM SnapshotLocalitySafety == Spec => []SnapshotLocality      BY Safety, PTL DEF Inv

(*-------------------------------------------------------------------------*)
(* At a settled point every node equals its local combine. This follows     *)
(* from SnapshotLocality, values = snapshot, and updated = Nodes.           *)
(*-------------------------------------------------------------------------*)
FixedPointConsistent == (changed = FALSE) => LocallyConsistent

THEOREM ConsistencyAtFixedPoint == Spec => []FixedPointConsistent
  <1>1. Inv => FixedPointConsistent
    <2> SUFFICES ASSUME Inv, changed = FALSE, NEW n \in Nodes
                 PROVE  values[n] = Combine(n, values)
      BY DEF FixedPointConsistent, LocallyConsistent
    <2>1. values = snapshot /\ updated = Nodes   BY DEF Inv, SettledOK
    <2>2. values[n] = Combine(n, snapshot)       BY <2>1 DEF Inv, SnapshotLocality
    <2> QED  BY <2>1, <2>2
  <1> QED  BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* Liveness proof for EventualSettledOrIterationLimit. A round spans three  *)
(* action classes, and node updates are quantified, so progress is composed *)
(* from the following leads-to chain:                                       *)
(*                                                                         *)
(*   (a) round = "idle" /\ changed /\ iteration < Max ~> round = "running"  *)
(*         -- a single-action WF1 instance on StartRound.                   *)
(*   (b) round = "running" ~> updated = Nodes                               *)
(*         -- finite assembly over the per-node fairness conjuncts, using  *)
(*            the finite CHOOSE-enumeration/cardinality argument.           *)
(*   (c) round = "running" /\ updated = Nodes ~> iteration advanced         *)
(*         -- a single-action WF1 instance on EndRound.                     *)
(*                                                                         *)
(* Node progress is established for a fixed n before finite-node assembly.  *)
(*-------------------------------------------------------------------------*)

\* While the round runs and n is un-updated, UpdateNode(n) is CONTINUOUSLY
\* enabled: no other action can disable it. StartRound and Terminate both
\* require round = "idle"; EndRound requires updated = Nodes, which n's own
\* absence forbids; and UpdateNode(m) for m # n leaves both conjuncts
\* standing. So the guard is stable and the single-action WF1 applies.
LEMMA NodeProgress ==
  ASSUME NEW n \in Nodes
  PROVE  Spec => ((round = "running" /\ n \notin updated) ~> (n \in updated))
  <1> DEFINE P == Inv /\ round = "running" /\ n \notin updated
  <1> DEFINE Q == n \in updated
  <1>1. P /\ [Next]_vars => (P' \/ Q')
    <2> SUFFICES ASSUME P, [Next]_vars PROVE P' \/ Q'  OBVIOUS
    <2>inv. Inv'  BY NextInv
    <2>0. CASE UNCHANGED vars
      BY <2>0, <2>inv DEF vars
    <2>1. CASE StartRound
      BY <2>1 DEF StartRound
    <2>2. CASE \E m \in Nodes : UpdateNode(m)
      <3>1. PICK m \in Nodes : UpdateNode(m)  BY <2>2
      <3>2. CASE m = n
        BY <3>1, <3>2 DEF UpdateNode
      <3>3. CASE m # n
        BY <3>1, <3>3, <2>inv DEF UpdateNode
      <3> QED  BY <3>2, <3>3
    <2>3. CASE EndRound
      BY <2>3 DEF EndRound
    <2>4. CASE Terminate
      BY <2>4 DEF Terminate
    <2> QED  BY <2>0, <2>1, <2>2, <2>3, <2>4 DEF Next
  <1>2. P /\ <<Next /\ UpdateNode(n)>>_vars => Q'
    BY DEF UpdateNode
  \* Expand the action and variable tuple to construct an enabled witness.
  <1>3. P => ENABLED <<UpdateNode(n)>>_vars
    <2> USE DEF UpdateNode, vars
    <2> SUFFICES ASSUME P PROVE ENABLED <<UpdateNode(n)>>_vars  OBVIOUS
    <2>t. values \in [Nodes -> 0..MaxValue] /\ snapshot \in [Nodes -> 0..MaxValue]
      BY DEF Inv, TypeInvariant
    <2>c. Combine(n, snapshot) \in 0..MaxValue
      BY <2>t, CombineTyped
    <2>g. round = "running" /\ n \notin updated
      OBVIOUS
    \* Adding n changes updated, so the enabled witness is non-stuttering.
    <2>d. updated \cup {n} # updated
      BY <2>g
    <2> QED
      BY <2>t, <2>c, <2>g, <2>d, ExpandENABLED
  \* Instantiate the per-node fairness conjunct before the temporal step.
  <1>wf. Spec => WF_vars(UpdateNode(n))
    BY DEF Spec, Fairness
  <1> QED
    BY <1>1, <1>2, <1>3, <1>wf, Safety, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* Assemble per-node progress into complete round coverage. Membership in  *)
(* updated is monotone while a round remains running.                       *)
(*-------------------------------------------------------------------------*)
LEMMA UpdatedStable ==
  Inv /\ [Next]_vars /\ round = "running" /\ round' = "running"
    => updated \subseteq updated'
  <1> SUFFICES ASSUME Inv, [Next]_vars, round = "running", round' = "running"
               PROVE  updated \subseteq updated'
    OBVIOUS
  <1>0. CASE UNCHANGED vars          BY <1>0 DEF vars
  <1>1. CASE StartRound              BY <1>1 DEF StartRound
  <1>2. CASE \E m \in Nodes : UpdateNode(m)
    BY <1>2 DEF UpdateNode
  <1>3. CASE EndRound                BY <1>3 DEF EndRound
  <1>4. CASE Terminate               BY <1>4 DEF Terminate
  <1> QED  BY <1>0, <1>1, <1>2, <1>3, <1>4 DEF Next

(*-------------------------------------------------------------------------*)
(* Enumerate the finite Nodes set and extend covered prefixes by induction. *)
(* Each induction hypothesis is one leads-to formula.                       *)
(*-------------------------------------------------------------------------*)
NodeCount == Cardinality(Nodes)
NodeOrder ==
  CHOOSE seq \in [1..NodeCount -> Nodes] :
    \A n \in Nodes : \E i \in 1..NodeCount : seq[i] = n
Prefix(c) == {NodeOrder[i] : i \in 1..c}

LEMMA NodeCountType == NodeCount \in Nat
  BY NodesFinite, FS_CardinalityType DEF NodeCount

LEMMA NodeOrderCover ==
  /\ NodeOrder \in [1..NodeCount -> Nodes]
  /\ \A n \in Nodes : \E i \in 1..NodeCount : NodeOrder[i] = n
  <1> DEFINE Q(seq) ==
        \A n \in Nodes : \E i \in 1..NodeCount : seq[i] = n
  <1>card. Cardinality(Nodes) = NodeCount  BY DEF NodeCount
  <1>bij. ExistsBijection(1..NodeCount, Nodes)
    BY NodesFinite, FS_CardinalityType, <1>card
  <1>ex. \E seq \in [1..NodeCount -> Nodes] : Q(seq)
    <2>1. PICK f \in Bijection(1..NodeCount, Nodes) : TRUE
      BY <1>bij DEF ExistsBijection
    <2>2. f \in Surjection(1..NodeCount, Nodes)
      BY <2>1 DEF Bijection
    <2>3. f \in [1..NodeCount -> Nodes] /\ Q(f)
      BY <2>2 DEF Surjection
    <2> QED  BY <2>3
  <1> QED  BY <1>ex DEF NodeOrder

LEMMA NodeOrderValue ==
  ASSUME NEW i \in 1..NodeCount
  PROVE NodeOrder[i] \in Nodes
  BY NodeOrderCover

LEMMA PrefixZero == Prefix(0) = {}
  BY DEF Prefix

LEMMA PrefixStep ==
  ASSUME NEW c \in Nat
  PROVE Prefix(c + 1) = Prefix(c) \cup {NodeOrder[c + 1]}
  BY DEF Prefix

LEMMA PrefixFull == Prefix(NodeCount) = Nodes
  <1> SUFFICES ASSUME NEW n
               PROVE n \in Prefix(NodeCount) <=> n \in Nodes
    OBVIOUS
  <1>A. ASSUME n \in Prefix(NodeCount) PROVE n \in Nodes
    <2>1. PICK i \in 1..NodeCount : NodeOrder[i] = n
      BY <1>A DEF Prefix
    <2>2. NodeOrder \in [1..NodeCount -> Nodes]
      BY NodeOrderCover
    <2> QED  BY <2>1, <2>2
  <1>B. ASSUME n \in Nodes PROVE n \in Prefix(NodeCount)
    BY <1>B, NodeOrderCover DEF Prefix
  <1> QED  BY <1>A, <1>B

LEMMA PrefixProgress ==
  \A r \in Nat : \A c \in Nat : c + 1 \in 1..NodeCount =>
    (Spec =>
      ((round = "running" /\ MaxIterations - iteration = r
          /\ Prefix(c) \subseteq updated)
        ~> (round = "running" /\ MaxIterations - iteration = r
              /\ Prefix(c + 1) \subseteq updated)))
PROOF
  <1> SUFFICES ASSUME NEW r \in Nat, NEW c \in Nat,
                       c + 1 \in 1..NodeCount
               PROVE Spec =>
                 ((round = "running" /\ MaxIterations - iteration = r
                    /\ Prefix(c) \subseteq updated)
                   ~> (round = "running" /\ MaxIterations - iteration = r
                         /\ Prefix(c + 1) \subseteq updated))
    OBVIOUS
  <1> DEFINE R == round = "running" /\ MaxIterations - iteration = r
  <1> DEFINE x == NodeOrder[c + 1]
  <1>xnode. x \in Nodes
    BY NodeOrderValue
  <1>prefix. Prefix(c + 1) = Prefix(c) \cup {x}
    BY PrefixStep
  <1> DEFINE A == Inv /\ R /\ Prefix(c) \subseteq updated
                        /\ x \notin updated
  <1> DEFINE B == R /\ Prefix(c) \cup {x} \subseteq updated
  <1>1. A /\ [Next]_vars => (A' \/ B')
    <2> SUFFICES ASSUME A, [Next]_vars PROVE A' \/ B'  OBVIOUS
    <2>inv. Inv'  BY NextInv
    <2>0. CASE UNCHANGED vars
      BY <2>0, <2>inv DEF vars
    <2>1. CASE StartRound
      BY <2>1 DEF StartRound
    <2>2. CASE \E m \in Nodes : UpdateNode(m)
      <3>1. PICK m \in Nodes : UpdateNode(m)  BY <2>2
      <3>A. CASE m = x
        BY <3>1, <3>A DEF UpdateNode
      <3>B. CASE m # x
        BY <3>1, <3>B, <2>inv DEF UpdateNode
      <3> QED  BY <3>A, <3>B
    <2>3. CASE EndRound
      BY <2>3, <1>xnode DEF EndRound
    <2>4. CASE Terminate
      BY <2>4 DEF Terminate
    <2> QED  BY <2>0, <2>1, <2>2, <2>3, <2>4 DEF Next
  <1>2. A /\ <<Next /\ UpdateNode(x)>>_vars => B'
    BY DEF UpdateNode
  <1>3. A => ENABLED <<UpdateNode(x)>>_vars
    <2> USE DEF UpdateNode, vars
    <2> SUFFICES ASSUME A PROVE ENABLED <<UpdateNode(x)>>_vars  OBVIOUS
    <2>t. values \in [Nodes -> 0..MaxValue]
             /\ snapshot \in [Nodes -> 0..MaxValue]
      BY DEF Inv, TypeInvariant
    <2>c. Combine(x, snapshot) \in 0..MaxValue
      BY <1>xnode, <2>t, CombineTyped
    <2>d. updated \cup {x} # updated
      BY DEF A
    <2> QED  BY <1>xnode, <2>t, <2>c, <2>d, ExpandENABLED
  <1>wf. Spec => WF_vars(UpdateNode(x))
    BY <1>xnode DEF Spec, Fairness
  <1>4. Spec => (A ~> B)
    BY <1>1, <1>2, <1>3, <1>wf, Safety, PTL DEF Spec
  <1>5. Inv /\ R /\ Prefix(c) \subseteq updated => A \/ B
    BY DEF A, B
  <1>6. B => R /\ Prefix(c + 1) \subseteq updated
    BY <1>prefix DEF B
  <1> QED  BY <1>4, <1>5, <1>6, Safety, PTL

LEMMA RoundCoverage ==
  \A r \in Nat : r \in 0..MaxIterations => (Spec =>
    ((round = "running" /\ MaxIterations - iteration = r)
      ~> (round = "running" /\ MaxIterations - iteration = r
            /\ updated = Nodes)))
PROOF
  <1> SUFFICES ASSUME NEW r \in Nat, r \in 0..MaxIterations
               PROVE Spec =>
                 ((round = "running" /\ MaxIterations - iteration = r)
                   ~> (round = "running" /\ MaxIterations - iteration = r
                         /\ updated = Nodes))
    OBVIOUS
  <1> DEFINE R == round = "running" /\ MaxIterations - iteration = r
  <1> DEFINE Covered(T) == R /\ T \subseteq updated
  <1> DEFINE P(c) == c \in 0..NodeCount
                         => (Spec => (R ~> Covered(Prefix(c))))
  <1> HIDE DEF P
  <1>base. P(0)
    <2>zero. 0 \in 0..NodeCount
      BY NodeCountType
    <2>now. R => Covered(Prefix(0))
      BY PrefixZero DEF Covered
    <2> QED  BY <2>zero, <2>now, PTL DEF P
  <1>step. \A c \in Nat : P(c) => P(c + 1)
    <2> SUFFICES ASSUME NEW c \in Nat, P(c) PROVE P(c + 1)
      OBVIOUS
    <2> SUFFICES ASSUME c + 1 \in 0..NodeCount,
                        Spec,
                        R ~> Covered(Prefix(c))
                 PROVE R ~> Covered(Prefix(c + 1))
      BY NodeCountType DEF P
    <2>prev. c \in 0..NodeCount  BY NodeCountType
    <2>index. c + 1 \in 1..NodeCount  OBVIOUS
    <2>ext. Spec => (Covered(Prefix(c)) ~> Covered(Prefix(c + 1)))
      <3>1. Spec =>
          ((round = "running" /\ MaxIterations - iteration = r
             /\ Prefix(c) \subseteq updated)
            ~> (round = "running" /\ MaxIterations - iteration = r
                  /\ Prefix(c + 1) \subseteq updated))
        BY <2>index, PrefixProgress
      <3> QED  BY <3>1, PTL DEF Covered, R
    <2> QED  BY <2>ext, PTL
  <1>all. \A c \in Nat : P(c)
    BY <1>base, <1>step, NatInduction
  <1>card. NodeCount \in Nat
    BY NodeCountType
  <1>pall. P(NodeCount)
    BY <1>all, <1>card
  <1>bound. NodeCount \in 0..NodeCount
    BY <1>card
  <1>covered. Spec => (R ~> Covered(Prefix(NodeCount)))
    BY <1>pall, <1>bound, PTL DEF P
  <1>same. Inv /\ Nodes \subseteq updated => updated = Nodes
    BY DEF Inv, TypeInvariant
  <1>prefixeq. Prefix(NodeCount) = Nodes
    BY PrefixFull
  <1>target. Inv /\ Covered(Prefix(NodeCount))
                  => R /\ updated = Nodes
    BY <1>same, <1>prefixeq DEF Covered
  <1> QED
    BY <1>covered, <1>target, Safety, PTL DEF R

(*-------------------------------------------------------------------------*)
(* Round progress indexed by MaxIterations - iteration. The final proof     *)
(* applies downward induction to this remaining-round measure.              *)
(*-------------------------------------------------------------------------*)
LEMMA StartRemainingProgress ==
  \A r \in 1..MaxIterations : Spec =>
    ((round = "idle" /\ changed = TRUE
       /\ MaxIterations - iteration = r)
      ~> (round = "running" /\ MaxIterations - iteration = r))
PROOF
  <1> SUFFICES ASSUME NEW r \in 1..MaxIterations
               PROVE Spec =>
                 ((round = "idle" /\ changed = TRUE
                    /\ MaxIterations - iteration = r)
                   ~> (round = "running"
                         /\ MaxIterations - iteration = r))
    OBVIOUS
  <1> DEFINE P == Inv /\ round = "idle" /\ changed = TRUE
                       /\ MaxIterations - iteration = r
  <1> DEFINE Q == round = "running" /\ MaxIterations - iteration = r
  <1>1. P /\ [Next]_vars => (P' \/ Q')
    <2> SUFFICES ASSUME P, [Next]_vars PROVE P' \/ Q'  OBVIOUS
    <2>inv. Inv'  BY NextInv
    <2>0. CASE UNCHANGED vars
      BY <2>0, <2>inv DEF vars
    <2>1. CASE StartRound
      BY <2>1 DEF StartRound
    <2>2. CASE \E t \in Nodes : UpdateNode(t)
      BY <2>2 DEF UpdateNode
    <2>3. CASE EndRound
      BY <2>3 DEF EndRound
    <2>4. CASE Terminate
      <3>term. changed = FALSE \/ iteration = MaxIterations
        BY <2>4 DEF Terminate
      <3>state. changed = TRUE /\ MaxIterations - iteration = r
        BY DEF P
      <3>nat. iteration \in Nat /\ iteration <= MaxIterations
        BY DEF P, Inv, TypeInvariant, IterationBound
      <3> QED  BY SMT, <3>term, <3>state, <3>nat, MaxIterationsType
    <2> QED  BY <2>0, <2>1, <2>2, <2>3, <2>4 DEF Next
  <1>2. P /\ <<Next /\ StartRound>>_vars => Q'
    BY DEF StartRound
  <1>3. P => ENABLED <<StartRound>>_vars
    <2> USE DEF StartRound, vars
    <2> SUFFICES ASSUME P PROVE ENABLED <<StartRound>>_vars  OBVIOUS
    <2>lt. iteration < MaxIterations
      BY SMT, MaxIterationsType DEF P, Inv, TypeInvariant, IterationBound
    <2>g. round = "idle" /\ changed = TRUE /\ iteration < MaxIterations
      BY <2>lt DEF P
    <2>d. "running" # round
      BY <2>g
    <2> QED  BY <2>g, <2>d, ExpandENABLED
  <1>wf. Spec => WF_vars(StartRound)
    BY DEF Spec, Fairness
  <1> QED
    BY <1>1, <1>2, <1>3, <1>wf, Safety, PTL DEF Spec

LEMMA EndRemainingProgress ==
  \A r \in 1..MaxIterations : Spec =>
    ((round = "running" /\ MaxIterations - iteration = r
       /\ updated = Nodes)
      ~> (MaxIterations - iteration = r - 1))
PROOF
  <1> SUFFICES ASSUME NEW r \in 1..MaxIterations
               PROVE Spec =>
                 ((round = "running" /\ MaxIterations - iteration = r
                    /\ updated = Nodes)
                   ~> (MaxIterations - iteration = r - 1))
    OBVIOUS
  <1> DEFINE P == Inv /\ round = "running"
                       /\ MaxIterations - iteration = r /\ updated = Nodes
  <1> DEFINE Q == MaxIterations - iteration = r - 1
  <1>1. P /\ [Next]_vars => (P' \/ Q')
    <2> SUFFICES ASSUME P, [Next]_vars PROVE P' \/ Q'  OBVIOUS
    <2>inv. Inv'  BY NextInv
    <2>0. CASE UNCHANGED vars
      BY <2>0, <2>inv DEF vars
    <2>1. CASE StartRound
      BY <2>1 DEF StartRound
    <2>2. CASE \E t \in Nodes : UpdateNode(t)
      BY <2>2 DEF UpdateNode
    <2>3. CASE EndRound
      BY SMT, <2>3, MaxIterationsType
         DEF P, Inv, TypeInvariant, IterationBound, EndRound
    <2>4. CASE Terminate
      BY <2>4 DEF Terminate
    <2> QED  BY <2>0, <2>1, <2>2, <2>3, <2>4 DEF Next
  <1>2. P /\ <<Next /\ EndRound>>_vars => Q'
    BY SMT, MaxIterationsType
       DEF P, Inv, TypeInvariant, IterationBound, EndRound
  <1>3. P => ENABLED <<EndRound>>_vars
    <2> USE DEF EndRound, vars
    <2> SUFFICES ASSUME P PROVE ENABLED <<EndRound>>_vars  OBVIOUS
    <2>g. round = "running" /\ updated = Nodes
      BY DEF P
    <2>d. "idle" # round
      BY <2>g
    <2> QED  BY <2>g, <2>d, ExpandENABLED
  <1>wf. Spec => WF_vars(EndRound)
    BY DEF Spec, Fairness
  <1> QED
    BY <1>1, <1>2, <1>3, <1>wf, Safety, PTL DEF Spec

LEMMA RunningRemainingProgress ==
  \A r \in 1..MaxIterations : Spec =>
    ((changed = TRUE /\ MaxIterations - iteration = r)
      ~> (round = "running" /\ MaxIterations - iteration = r))
  <1> SUFFICES ASSUME NEW r \in 1..MaxIterations
               PROVE Spec =>
                 ((changed = TRUE /\ MaxIterations - iteration = r)
                   ~> (round = "running" /\ MaxIterations - iteration = r))
    OBVIOUS
  <1>1. Spec =>
      ((round = "idle" /\ changed = TRUE
         /\ MaxIterations - iteration = r)
        ~> (round = "running" /\ MaxIterations - iteration = r))
    BY StartRemainingProgress
  <1>2. Inv /\ changed = TRUE /\ MaxIterations - iteration = r
           => \/ round = "running" /\ MaxIterations - iteration = r
              \/ round = "idle" /\ changed = TRUE
                   /\ MaxIterations - iteration = r
    BY DEF Inv, TypeInvariant
  <1> QED  BY <1>1, <1>2, Safety, PTL

LEMMA RemainingProgress ==
  \A r \in Nat : r \in 1..MaxIterations => (Spec =>
    ((changed = TRUE /\ MaxIterations - iteration = r)
      ~> (MaxIterations - iteration = r - 1)))
  <1> SUFFICES ASSUME NEW r \in Nat, r \in 1..MaxIterations
               PROVE Spec =>
                 ((changed = TRUE /\ MaxIterations - iteration = r)
                   ~> (MaxIterations - iteration = r - 1))
    OBVIOUS
  <1>run. Spec =>
      ((changed = TRUE /\ MaxIterations - iteration = r)
        ~> (round = "running" /\ MaxIterations - iteration = r))
    BY RunningRemainingProgress
  <1>rbound. r \in 0..MaxIterations
    BY MaxIterationsType
  <1>cover. Spec =>
      ((round = "running" /\ MaxIterations - iteration = r)
        ~> (round = "running" /\ MaxIterations - iteration = r
              /\ updated = Nodes))
    BY <1>rbound, RoundCoverage
  <1>end. Spec =>
      ((round = "running" /\ MaxIterations - iteration = r
         /\ updated = Nodes)
        ~> (MaxIterations - iteration = r - 1))
    BY EndRemainingProgress
  <1> QED  BY <1>run, <1>cover, <1>end, PTL

Done == changed = FALSE \/ iteration = MaxIterations

LEMMA RemainingSplit ==
  \A r \in Nat : r \in 1..MaxIterations => (Spec =>
    []((Done \/ MaxIterations - iteration = r)
         => Done \/ (changed = TRUE /\ MaxIterations - iteration = r)))
  <1> SUFFICES ASSUME NEW r \in Nat, r \in 1..MaxIterations
               PROVE Spec =>
                 []((Done \/ MaxIterations - iteration = r)
                      => Done \/ (changed = TRUE
                                   /\ MaxIterations - iteration = r))
    OBVIOUS
  <1>state. Inv /\ (Done \/ MaxIterations - iteration = r)
             => Done \/ (changed = TRUE /\ MaxIterations - iteration = r)
    BY DEF Done, Inv, TypeInvariant
  <1> QED  BY <1>state, Safety, PTL

THEOREM EventualSettledOrIterationLimitProved == Spec => EventualSettledOrIterationLimit
PROOF
  <1> DEFINE P(m) == Spec => <>(Done \/ MaxIterations - iteration = m)
  <1> HIDE DEF P
  <1>base. P(MaxIterations)
    <2> SUFFICES ASSUME Spec
                 PROVE <>(Done \/ MaxIterations - iteration = MaxIterations)
      BY DEF P
    <2>1. Init => (MaxIterations - iteration = MaxIterations)
      BY MaxIterationsType DEF Init
    <2> QED  BY <2>1, PTL DEF Spec
  <1>step. \A r \in 1..MaxIterations : P(r) => P(r - 1)
    <2> SUFFICES ASSUME NEW r \in Nat, r \in 1..MaxIterations
                 PROVE P(r) => P(r - 1)
      OBVIOUS
    <2> SUFFICES ASSUME Spec, <>(Done \/ MaxIterations - iteration = r)
                 PROVE <>(Done \/ MaxIterations - iteration = r - 1)
      BY DEF P
    <2>advance. Spec =>
        ((changed = TRUE /\ MaxIterations - iteration = r)
          ~> (MaxIterations - iteration = r - 1))
      BY RemainingProgress
    <2>boxSplit. Spec =>
        []((Done \/ MaxIterations - iteration = r)
             => Done \/ (changed = TRUE /\ MaxIterations - iteration = r))
      BY RemainingSplit
    <2>splitLead. Spec =>
        ((Done \/ MaxIterations - iteration = r)
          ~> (Done \/ (changed = TRUE /\ MaxIterations - iteration = r)))
      BY <2>boxSplit, PTL
    <2>advanceLead. Spec =>
        ((Done \/ (changed = TRUE /\ MaxIterations - iteration = r))
          ~> (Done \/ MaxIterations - iteration = r - 1))
      BY <2>advance, PTL
    <2> QED  BY <2>splitLead, <2>advanceLead, PTL
  <1>dn. P(0)
    BY <1>base, <1>step, MaxIterationsType, DownwardNatInduction
  <1>zero. Spec =>
      [](MaxIterations - iteration = 0 => iteration = MaxIterations)
    <2>1. Inv =>
        (MaxIterations - iteration = 0 => iteration = MaxIterations)
      BY SMT, MaxIterationsType DEF Inv, TypeInvariant, IterationBound
    <2> QED  BY <2>1, Safety, PTL DEF Spec
  <1> QED  BY <1>dn, <1>zero, PTL DEF P, Done, EventualSettledOrIterationLimit
====
