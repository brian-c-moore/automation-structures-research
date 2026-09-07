---- MODULE EquivalenceClass_Proof ----
(* TLAPS proof of EquivalenceClass (union-find, union-by-rank) safety:
   TypeInvariant, RepresentativeIdempotence, Symmetry, Transitivity,
   RankMonotonicity, RepresentativeRootedness.

   Semantic guide: crate://automation-structures/0.2.3/src/compositions/equivalence_class.rs.

   The crux is that Rep(e) = RepFun[MaxOps+1][e] is a root.  The inductive
   invariant adds three strengthenings to TypeInvariant:
     StrictRank   : a non-root has STRICTLY smaller rank than its parent
                    (RankMonotonicity is the <= weakening, the cfg invariant);
     OpsDoneBound : ops_done <= MaxOps;
     RankOpsBound : rnk[e] <= ops_done   (each equal-rank merge raises exactly
                    one rank by one and consumes one op).
   Together rnk[e] <= MaxOps for every e.  StrictRank makes each parent hop
   strictly raise the rank, so a chain of MaxOps+1 non-root hops would reach
   rank > MaxOps -- impossible; hence RepFun[MaxOps+1][e] is a root (RepRoot).
   RepresentativeIdempotence and RepresentativeRootedness follow from RepRoot; RankMonotonicity is
   StrictRank weakened; Symmetry and Transitivity are properties of =. *)
EXTENDS EquivalenceClass, Naturals, NaturalsInduction, TLAPS

ASSUME MaxOpsType == MaxOps \in Nat

\* Arithmetic fact used by the equal-merge case of RankOpsBound.
LEMMA NatLePlusOne == ASSUME NEW x \in Nat, NEW y \in Nat, x <= y PROVE x <= y + 1
  OBVIOUS

\* ---- Inductive strengthenings (proof machinery; cfg invariants are targets) -
StrictRank   == \A e \in Elements : parent[e] /= e => rnk[e] < rnk[parent[e]]
OpsDoneBound == ops_done <= MaxOps
RankOpsBound == \A e \in Elements : rnk[e] <= ops_done

Inv == TypeInvariant /\ StrictRank /\ OpsDoneBound /\ RankOpsBound

\* ---- RepFun recursion equation (FiniteNatInductiveDef) --------------------
\* One parent-hop layer: the Def of the fixpoint.
RepStep(prev) == [e \in Elements |-> IF parent[e] = e THEN e ELSE prev[parent[e]]]

LEMMA RepFunDefConclusion ==
  FiniteNatInductiveDefConclusion(RepFun, [e \in Elements |-> e],
                                  LAMBDA prev, k : RepStep(prev), 0, MaxOps + 1)
  <1>1. FiniteNatInductiveDefHypothesis(RepFun, [e \in Elements |-> e],
                                        LAMBDA prev, k : RepStep(prev), 0, MaxOps + 1)
    BY DEF FiniteNatInductiveDefHypothesis, RepFun, RepStep
  <1>2. MaxOps + 1 \in Nat
    BY MaxOpsType
  <1> QED  BY <1>1, <1>2, FiniteNatInductiveDef

\* Per-application unfolding of RepFun.
LEMMA RepFunApp ==
  ASSUME NEW k \in 0..(MaxOps + 1), NEW e \in Elements
  PROVE  RepFun[k][e] = IF k = 0 THEN e
                        ELSE IF parent[e] = e THEN e ELSE RepFun[k - 1][parent[e]]
  <1>1. RepFun[k] = IF k = 0 THEN [x \in Elements |-> x] ELSE RepStep(RepFun[k - 1])
    BY RepFunDefConclusion DEF FiniteNatInductiveDefConclusion
  <1>2. CASE k = 0
    BY <1>1, <1>2
  <1>3. CASE k # 0
    <2>1. RepFun[k] = RepStep(RepFun[k - 1])  BY <1>1, <1>3
    <2> QED  BY <2>1, <1>3 DEF RepStep
  <1> QED  BY <1>2, <1>3

\* ---- RepFun stays inside Elements -----------------------------------------
LEMMA RepFunType ==
  ASSUME TypeInvariant
  PROVE  \A k \in 0..(MaxOps + 1) : \A e \in Elements : RepFun[k][e] \in Elements
  <1> DEFINE Q(k) == k \in 0..(MaxOps + 1) =>
                       \A e \in Elements : RepFun[k][e] \in Elements
  <1>1. Q(0)
    <2> SUFFICES ASSUME 0 \in 0..(MaxOps + 1), NEW e \in Elements
                 PROVE  RepFun[0][e] \in Elements
      OBVIOUS
    <2> QED  BY RepFunApp
  <1>2. ASSUME NEW k \in Nat, Q(k) PROVE Q(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..(MaxOps + 1), NEW e \in Elements
                 PROVE  RepFun[k + 1][e] \in Elements
      OBVIOUS
    <2>k. k \in 0..(MaxOps + 1)  BY MaxOpsType
    <2>pe. parent[e] \in Elements  BY DEF TypeInvariant
    <2>1. RepFun[k + 1][e] = IF parent[e] = e THEN e ELSE RepFun[k][parent[e]]
      BY RepFunApp, MaxOpsType
    <2>2. RepFun[k][parent[e]] \in Elements  BY <2>k, <2>pe, Q(k)
    <2> QED  BY <2>1, <2>2
  <1>3. \A k \in Nat : Q(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3, MaxOpsType

\* ---- Rank-climb: each hop adds >= 1 to the rank until a root is reached ----
LEMMA RankClimb ==
  ASSUME TypeInvariant, StrictRank
  PROVE  \A k \in 0..(MaxOps + 1) : \A e \in Elements :
           parent[RepFun[k][e]] = RepFun[k][e] \/ rnk[RepFun[k][e]] >= rnk[e] + k
  <1> DEFINE Q(k) == k \in 0..(MaxOps + 1) =>
                       \A e \in Elements :
                         parent[RepFun[k][e]] = RepFun[k][e]
                           \/ rnk[RepFun[k][e]] >= rnk[e] + k
  <1>1. Q(0)
    <2> SUFFICES ASSUME 0 \in 0..(MaxOps + 1), NEW e \in Elements
                 PROVE  parent[RepFun[0][e]] = RepFun[0][e]
                          \/ rnk[RepFun[0][e]] >= rnk[e] + 0
      OBVIOUS
    <2>1. RepFun[0][e] = e  BY RepFunApp
    <2>2. rnk[e] \in Nat    BY DEF TypeInvariant
    <2> QED  BY <2>1, <2>2
  <1>2. ASSUME NEW k \in Nat, Q(k) PROVE Q(k + 1)
    <2> SUFFICES ASSUME k + 1 \in 0..(MaxOps + 1), NEW e \in Elements
                 PROVE  parent[RepFun[k + 1][e]] = RepFun[k + 1][e]
                          \/ rnk[RepFun[k + 1][e]] >= rnk[e] + (k + 1)
      OBVIOUS
    <2>k. k \in 0..(MaxOps + 1)  BY MaxOpsType
    <2>app. RepFun[k + 1][e] = IF parent[e] = e THEN e ELSE RepFun[k][parent[e]]
      BY RepFunApp, MaxOpsType
    <2>A. CASE parent[e] = e
      <3>1. RepFun[k + 1][e] = e  BY <2>app, <2>A
      <3> QED  BY <3>1, <2>A
    <2>B. CASE parent[e] # e
      <3>pe. parent[e] \in Elements  BY DEF TypeInvariant
      <3>1. RepFun[k + 1][e] = RepFun[k][parent[e]]  BY <2>app, <2>B
      <3>ih. parent[RepFun[k][parent[e]]] = RepFun[k][parent[e]]
               \/ rnk[RepFun[k][parent[e]]] >= rnk[parent[e]] + k
        BY <2>k, <3>pe, Q(k)
      <3>strict. rnk[e] < rnk[parent[e]]  BY <2>B DEF StrictRank
      <3>nat. rnk[e] \in Nat /\ rnk[parent[e]] \in Nat
        BY <3>pe DEF TypeInvariant
      <3>B1. CASE parent[RepFun[k][parent[e]]] = RepFun[k][parent[e]]
        BY <3>1, <3>B1
      <3>B2. CASE rnk[RepFun[k][parent[e]]] >= rnk[parent[e]] + k
        <4>1. rnk[RepFun[k + 1][e]] >= rnk[parent[e]] + k  BY <3>1, <3>B2
        <4>2. RepFun[k + 1][e] \in Elements  BY RepFunType
        <4>3. rnk[RepFun[k + 1][e]] \in Nat  BY <4>2 DEF TypeInvariant
        <4> QED  BY <4>1, <3>strict, <3>nat, <4>3, MaxOpsType
      <3> QED  BY <3>ih, <3>B1, <3>B2
    <2> QED  BY <2>A, <2>B
  <1>3. \A k \in Nat : Q(k)  BY <1>1, <1>2, NatInduction
  <1> QED  BY <1>3, MaxOpsType

\* ---- RepRoot: Rep(e) is a root ; RepOfRoot: Rep of a root is itself --------
LEMMA RepRoot ==
  ASSUME Inv, NEW e \in Elements
  PROVE  parent[Rep(e)] = Rep(e)
  <1> USE DEF Inv, OpsDoneBound, RankOpsBound
  <1>top. MaxOps + 1 \in 0..(MaxOps + 1)  BY MaxOpsType
  <1>climb. parent[RepFun[MaxOps + 1][e]] = RepFun[MaxOps + 1][e]
              \/ rnk[RepFun[MaxOps + 1][e]] >= rnk[e] + (MaxOps + 1)
    BY <1>top, RankClimb DEF Inv
  <1>inE. RepFun[MaxOps + 1][e] \in Elements  BY <1>top, RepFunType DEF Inv
  <1>bound. rnk[RepFun[MaxOps + 1][e]] <= MaxOps
    <2>1. rnk[RepFun[MaxOps + 1][e]] <= ops_done  BY <1>inE DEF RankOpsBound
    <2>2. ops_done <= MaxOps  BY DEF OpsDoneBound
    <2>3. rnk[RepFun[MaxOps + 1][e]] \in Nat /\ ops_done \in Nat
      BY <1>inE DEF TypeInvariant
    <2> QED  BY <2>1, <2>2, <2>3, MaxOpsType
  <1>nat. rnk[e] \in Nat /\ rnk[RepFun[MaxOps + 1][e]] \in Nat
    BY <1>inE DEF TypeInvariant
  <1>refute. ~(rnk[RepFun[MaxOps + 1][e]] >= rnk[e] + (MaxOps + 1))
    BY <1>bound, <1>nat, MaxOpsType
  <1> QED  BY <1>climb, <1>refute DEF Rep

LEMMA RepOfRoot ==
  ASSUME TypeInvariant, NEW r \in Elements, parent[r] = r
  PROVE  Rep(r) = r
  <1>top. MaxOps + 1 \in 0..(MaxOps + 1)  BY MaxOpsType
  <1>1. RepFun[MaxOps + 1][r] = IF MaxOps + 1 = 0 THEN r
                                ELSE IF parent[r] = r THEN r ELSE RepFun[MaxOps][parent[r]]
    BY <1>top, RepFunApp
  <1>2. MaxOps + 1 # 0  BY MaxOpsType
  <1> QED  BY <1>1, <1>2 DEF Rep

\* ---- The module's invariants other than TypeInvariant follow from Inv ------
LEMMA InvImpliesCfg ==
  ASSUME Inv
  PROVE  RepresentativeIdempotence /\ Symmetry /\ Transitivity /\ RankMonotonicity /\ RepresentativeRootedness
  <1>root. \A e \in Elements : parent[Rep(e)] = Rep(e)
    BY RepRoot
  <1>repE. \A e \in Elements : Rep(e) \in Elements
    <2> SUFFICES ASSUME NEW e \in Elements PROVE Rep(e) \in Elements  OBVIOUS
    <2>1. MaxOps + 1 \in 0..(MaxOps + 1)  BY MaxOpsType
    <2> QED  BY <2>1, RepFunType DEF Inv, Rep
  <1>refl. RepresentativeIdempotence
    <2> SUFFICES ASSUME NEW e \in Elements PROVE Rep(e) = Rep(Rep(e))
      BY DEF RepresentativeIdempotence
    <2>1. parent[Rep(e)] = Rep(e)  BY <1>root
    <2>2. Rep(e) \in Elements       BY <1>repE
    <2>3. Rep(Rep(e)) = Rep(e)      BY <2>1, <2>2, RepOfRoot DEF Inv
    <2> QED  BY <2>3
  <1>sym. Symmetry
    BY DEF Symmetry
  <1>trans. Transitivity
    BY DEF Transitivity
  <1>rankmono. RankMonotonicity
    BY DEF RankMonotonicity, Inv, StrictRank, TypeInvariant
  <1>path. RepresentativeRootedness
    BY <1>root DEF RepresentativeRootedness
  <1> QED  BY <1>refl, <1>sym, <1>trans, <1>rankmono, <1>path

\* ---- Init establishes Inv -------------------------------------------------
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1> USE DEF Init
  <1>1. TypeInvariant
    BY DEF TypeInvariant
  <1>2. StrictRank
    \* parent[e] = e for every e, so the antecedent parent[e] /= e is false.
    BY DEF StrictRank
  <1>3. OpsDoneBound
    BY MaxOpsType DEF OpsDoneBound
  <1>4. RankOpsBound
    BY DEF RankOpsBound
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

\* ---- Next preserves Inv ---------------------------------------------------
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, StrictRank, OpsDoneBound, RankOpsBound
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE \E a \in Elements, b \in Elements : Union(a, b)
    <2> SUFFICES ASSUME NEW a \in Elements, NEW b \in Elements, Union(a, b)
                 PROVE  Inv'
      BY <1>1
    <2> DEFINE ra == Rep(a)
    <2> DEFINE rb == Rep(b)
    <2>raE. ra \in Elements  BY RepFunType, MaxOpsType DEF Rep
    <2>rbE. rb \in Elements  BY RepFunType, MaxOpsType DEF Rep
    <2>raRoot. parent[ra] = ra  BY RepRoot DEF Inv
    <2>rbRoot. parent[rb] = rb  BY RepRoot DEF Inv
    <2>guard. ra /= rb  BY DEF Union
    <2>ops. ops_done < MaxOps  BY DEF Union
    <2>opsP. ops_done' = ops_done + 1  BY DEF Union
    <2>rnkNat. rnk[ra] \in Nat /\ rnk[rb] \in Nat  BY <2>raE, <2>rbE DEF TypeInvariant
    \* Common: OpsDoneBound' and ops_done typing.
    <2>obP. ops_done' <= MaxOps  BY <2>ops, <2>opsP, MaxOpsType DEF OpsDoneBound
    \* Trichotomy case-split on rnk[ra] vs rnk[rb].
    <2>c1. CASE rnk[ra] < rnk[rb]
      <3>pp. parent' = [parent EXCEPT ![ra] = rb]  BY <2>c1 DEF Union
      <3>rp. rnk' = rnk  BY <2>c1 DEF Union
      <3>1. TypeInvariant'
        <4>1. parent' \in [Elements -> Elements]  BY <3>pp, <2>raE, <2>rbE
        <4> QED  BY <4>1, <3>rp, <2>opsP DEF TypeInvariant
      <3>2. StrictRank'
        <4> SUFFICES ASSUME NEW e \in Elements, parent'[e] /= e
                     PROVE  rnk'[e] < rnk'[parent'[e]]
          BY <3>rp DEF StrictRank
        <4>pv. parent'[e] = IF e = ra THEN rb ELSE parent[e]
          BY <3>pp, <2>raE
        <4>A. CASE e = ra
          <5>1. parent'[e] = rb  BY <4>pv, <4>A
          <5> QED  BY <5>1, <3>rp, <2>c1, <4>A
        <4>B. CASE e # ra
          <5>1. parent'[e] = parent[e]  BY <4>pv, <4>B
          <5>2. parent[e] # e  BY <5>1
          <5>3. rnk[e] < rnk[parent[e]]  BY <5>2 DEF StrictRank
          <5> QED  BY <5>1, <5>3, <3>rp
        <4> QED  BY <4>A, <4>B
      <3>3. OpsDoneBound'  BY <2>obP DEF OpsDoneBound
      <3>4. RankOpsBound'
        <4> SUFFICES ASSUME NEW e \in Elements PROVE rnk'[e] <= ops_done'
          BY <3>rp DEF RankOpsBound
        <4>1. rnk[e] <= ops_done  BY DEF RankOpsBound
        <4> QED  BY <4>1, <3>rp, <2>opsP, <2>ops, MaxOpsType
      <3> QED  BY <3>1, <3>2, <3>3, <3>4 DEF Inv
    <2>c2. CASE rnk[ra] > rnk[rb]
      <3>pp. parent' = [parent EXCEPT ![rb] = ra]  BY <2>c2, <2>rnkNat DEF Union
      <3>rp. rnk' = rnk  BY <2>c2, <2>rnkNat DEF Union
      <3>1. TypeInvariant'
        <4>1. parent' \in [Elements -> Elements]  BY <3>pp, <2>raE, <2>rbE
        <4> QED  BY <4>1, <3>rp, <2>opsP DEF TypeInvariant
      <3>2. StrictRank'
        <4> SUFFICES ASSUME NEW e \in Elements, parent'[e] /= e
                     PROVE  rnk'[e] < rnk'[parent'[e]]
          BY <3>rp DEF StrictRank
        <4>pv. parent'[e] = IF e = rb THEN ra ELSE parent[e]
          BY <3>pp, <2>rbE
        <4>A. CASE e = rb
          <5>1. parent'[e] = ra  BY <4>pv, <4>A
          <5> QED  BY <5>1, <3>rp, <2>c2, <4>A
        <4>B. CASE e # rb
          <5>1. parent'[e] = parent[e]  BY <4>pv, <4>B
          <5>2. parent[e] # e  BY <5>1
          <5>3. rnk[e] < rnk[parent[e]]  BY <5>2 DEF StrictRank
          <5> QED  BY <5>1, <5>3, <3>rp
        <4> QED  BY <4>A, <4>B
      <3>3. OpsDoneBound'  BY <2>obP DEF OpsDoneBound
      <3>4. RankOpsBound'
        <4> SUFFICES ASSUME NEW e \in Elements PROVE rnk'[e] <= ops_done'
          BY <3>rp DEF RankOpsBound
        <4>1. rnk[e] <= ops_done  BY DEF RankOpsBound
        <4> QED  BY <4>1, <3>rp, <2>opsP, <2>ops, MaxOpsType
      <3> QED  BY <3>1, <3>2, <3>3, <3>4 DEF Inv
    <2>c3. CASE rnk[ra] = rnk[rb]
      <3>pp. parent' = [parent EXCEPT ![rb] = ra]  BY <2>c3, <2>rnkNat DEF Union
      <3>rp. rnk' = [rnk EXCEPT ![ra] = rnk[ra] + 1]  BY <2>c3, <2>rnkNat DEF Union
      <3>rv. \A x \in Elements : rnk'[x] = IF x = ra THEN rnk[ra] + 1 ELSE rnk[x]
        BY <3>rp, <2>raE
      <3>1. TypeInvariant'
        <4>1. parent' \in [Elements -> Elements]  BY <3>pp, <2>raE, <2>rbE
        <4>2. rnk' \in [Elements -> Nat]  BY <3>rp, <2>raE DEF TypeInvariant
        <4> QED  BY <4>1, <4>2, <2>opsP DEF TypeInvariant
      <3>2. StrictRank'
        <4> SUFFICES ASSUME NEW e \in Elements, parent'[e] /= e
                     PROVE  rnk'[e] < rnk'[parent'[e]]
          BY DEF StrictRank
        <4>pv. parent'[e] = IF e = rb THEN ra ELSE parent[e]
          BY <3>pp, <2>rbE
        <4>A. CASE e = rb
          <5>1. parent'[e] = ra  BY <4>pv, <4>A
          <5>2. rnk'[e] = rnk[rb]  BY <3>rv, <4>A, <2>guard
          <5>3. rnk'[ra] = rnk[ra] + 1  BY <3>rv, <2>raE
          <5>4. rnk[rb] < rnk[ra] + 1  BY <2>c3, <2>rnkNat
          <5> QED  BY <5>1, <5>2, <5>3, <5>4
        <4>B. CASE e # rb
          <5>1. parent'[e] = parent[e]  BY <4>pv, <4>B
          <5>2. parent[e] # e  BY <5>1
          <5>3. rnk[e] < rnk[parent[e]]  BY <5>2 DEF StrictRank
          <5>peE. parent[e] \in Elements  BY DEF TypeInvariant
          \* e # ra: a root ra has parent[ra]=ra, so e=ra would make parent'[e]=e.
          <5>ne. e # ra
            <6>1. parent[ra] = ra  BY <2>raRoot
            <6> QED  BY <6>1, <5>1, <4>B
          <5>4. rnk'[e] = rnk[e]  BY <3>rv, <5>ne
          <5>5. rnk'[parent[e]] = IF parent[e] = ra THEN rnk[ra] + 1 ELSE rnk[parent[e]]
            BY <3>rv, <5>peE
          <5>6. rnk[e] < rnk'[parent[e]]
            <6>A. CASE parent[e] = ra
              <7>1. rnk'[parent[e]] = rnk[ra] + 1  BY <5>5, <6>A
              <7>2. rnk[e] < rnk[ra]  BY <5>3, <6>A
              <7> QED  BY <7>1, <7>2, <2>rnkNat, <5>peE DEF TypeInvariant
            <6>B. CASE parent[e] # ra
              <7>1. rnk'[parent[e]] = rnk[parent[e]]  BY <5>5, <6>B
              <7> QED  BY <7>1, <5>3
            <6> QED  BY <6>A, <6>B
          <5> QED  BY <5>1, <5>4, <5>6
        <4> QED  BY <4>A, <4>B
      <3>3. OpsDoneBound'  BY <2>obP DEF OpsDoneBound
      <3>4. RankOpsBound'
        <4> SUFFICES ASSUME NEW e \in Elements PROVE rnk'[e] <= ops_done'
          BY DEF RankOpsBound
        <4>A. CASE e = ra
          <5>1. rnk'[e] = rnk[ra] + 1  BY <3>rv, <4>A, <2>raE
          <5>2. rnk[ra] <= ops_done  BY <2>raE DEF RankOpsBound
          <5>3. rnk[ra] \in Nat /\ ops_done \in Nat  BY <2>raE DEF TypeInvariant
          <5>4. rnk[ra] + 1 <= ops_done + 1  BY <5>2, <5>3
          <5>5. ops_done' = ops_done + 1  BY <2>opsP
          <5> QED  BY <5>1, <5>4, <5>5
        <4>B. CASE e # ra
          <5>1. rnk'[e] = rnk[e]  BY <3>rv, <4>B
          <5>2. rnk[e] <= ops_done  BY DEF RankOpsBound
          <5>3. rnk[e] \in Nat /\ ops_done \in Nat  BY DEF TypeInvariant
          <5>4. rnk'[e] <= ops_done + 1  BY <5>1, <5>2, <5>3, NatLePlusOne
          <5>5. ops_done' = ops_done + 1  BY <2>opsP
          <5> QED  BY <5>4, <5>5
        <4> QED  BY <4>A, <4>B
      <3> QED  BY <3>1, <3>2, <3>3, <3>4 DEF Inv
    <2> QED  BY <2>c1, <2>c2, <2>c3, <2>rnkNat
  <1>2. CASE Idle
    BY <1>2 DEF Idle, vars
  <1>X. CASE Next
    BY <1>X, <1>1, <1>2 DEF Next
  <1> QED  BY <1>0, <1>X

\* ---- Safety, and one corollary per invariant EquivalenceClass defines -----
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'   BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv
THEOREM RepresentativeIdempotenceSafety == Spec => []RepresentativeIdempotence
  <1>1. Inv => RepresentativeIdempotence  BY InvImpliesCfg
  <1> QED  BY Safety, <1>1, PTL
THEOREM SymmetrySafety == Spec => []Symmetry
  <1>1. Inv => Symmetry  BY InvImpliesCfg
  <1> QED  BY Safety, <1>1, PTL
THEOREM TransitivitySafety == Spec => []Transitivity
  <1>1. Inv => Transitivity  BY InvImpliesCfg
  <1> QED  BY Safety, <1>1, PTL
THEOREM RankMonotonicitySafety == Spec => []RankMonotonicity
  <1>1. Inv => RankMonotonicity  BY InvImpliesCfg
  <1> QED  BY Safety, <1>1, PTL
THEOREM RepresentativeRootednessSafety == Spec => []RepresentativeRootedness
  <1>1. Inv => RepresentativeRootedness  BY InvImpliesCfg
  <1> QED  BY Safety, <1>1, PTL
====
