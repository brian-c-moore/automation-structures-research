---- MODULE CommitChallengeResponseFlow_Proof ----
(***************************************************************************
  TLAPS proof of safety for the CommitChallengeResponseFlow composition
  (the composition taxonomy, Ed25519 / Schnorr; supplementary-research/studies/domain-corpora/cryptography/tla/compositions/).

  Discharges the THEOREM declared in CommitChallengeResponseFlow.tla:
      Spec => [](TypeInvariant /\ PhaseOrdering /\ RIsCommitted
                                /\ ChallengeFromValues /\ ResponseFromValues)

  Inductive strengthening: none beyond the cfg's five invariants. The
  five are jointly inductive without further strengthening; the phase
  state machine determines the values of r_scalar / R_point / c_scalar
  / s_scalar at each phase, and the invariants are conditional on phase.

  This proof module covers the flow half of the CommitChallengeResponse
  decomposition. It mirrors EncryptThenAuthenticate_Proof.tla's three-phase
  ordering pattern and GroupDistributivity's GroupOp / ScalarMult
  helper-lemma shape.
 ***************************************************************************)
EXTENDS CommitChallengeResponseFlow, Naturals, Sequences, FiniteSets, TLAPS

ASSUME BitsPerScalarAss == BitsPerScalar \in Nat /\ BitsPerScalar = 4

\* Helper lemmas: structural typing for the topology.
LEMMA GroupOpType ==
    \A a \in GroupElement, b \in GroupElement : GroupOp[<<a, b>>] \in GroupElement
  BY DEF GroupOp, GroupElement

LEMMA ScalarMultType ==
    \A k \in ScalarValue, p \in GroupElement : ScalarMult[<<k, p>>] \in GroupElement
  BY DEF ScalarMult, ScalarValue, GroupElement, L

LEMMA HashType ==
    \A p \in GroupElement \X GroupElement \X GroupElement : Hash[p] \in ScalarValue
  BY DEF Hash, ScalarValue, L

LEMMA ScalarAddType ==
    \A a \in ScalarValue, b \in ScalarValue : ScalarAdd(a, b) \in ScalarValue
  BY DEF ScalarAdd, ScalarValue, L

LEMMA ScalarMulType ==
    \A a \in ScalarValue, b \in ScalarValue : ScalarMul(a, b) \in ScalarValue
  BY DEF ScalarMul, ScalarValue, L

LEMMA GroupIdentityType == GroupIdentity \in GroupElement
  BY DEF GroupIdentity, GroupElement

LEMMA GType == G \in GroupElement
  BY DEF G, GroupElement

LEMMA AType == A \in GroupElement
  BY DEF A, GroupElement

LEMMA M_hashType == M_hash \in GroupElement
  BY DEF M_hash, GroupElement

LEMMA a_secretType == a_secret \in ScalarValue
  BY DEF a_secret, ScalarValue, L

LEMMA r_nonceType == r_nonce \in ScalarValue
  BY DEF r_nonce, ScalarValue, L

\* Inductive invariant.
Inv == TypeInvariant /\ PhaseOrdering /\ RIsCommitted
       /\ ChallengeFromValues /\ ResponseFromValues

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY GroupIdentityType DEF Init, TypeInvariant, ScalarValue, L
  <1>2. PhaseOrdering
    BY DEF Init, PhaseOrdering
  <1>3. RIsCommitted
    \* phase = "commit"; antecedent of the implication is false.
    BY DEF Init, RIsCommitted
  <1>4. ChallengeFromValues
    BY DEF Init, ChallengeFromValues
  <1>5. ResponseFromValues
    BY DEF Init, ResponseFromValues
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, PhaseOrdering, RIsCommitted,
              ChallengeFromValues, ResponseFromValues
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE CommitStep
    <2>a. phase = "commit"                                BY <1>A DEF CommitStep
    <2>b. r_scalar' = r_nonce                             BY <1>A DEF CommitStep
    <2>c. R_point' = ScalarMult[<<r_nonce, G>>]           BY <1>A DEF CommitStep
    <2>d. phase' = "challenge"                            BY <1>A DEF CommitStep
    <2>e. UNCHANGED <<c_scalar, s_scalar>>                BY <1>A DEF CommitStep
    <2>f. r_nonce \in ScalarValue                         BY r_nonceType
    <2>g. G \in GroupElement                              BY GType
    <2>h. R_point' \in GroupElement                       BY <2>c, <2>f, <2>g, ScalarMultType
    <2>1. TypeInvariant'
      BY <2>b, <2>c, <2>d, <2>e, <2>f, <2>h
    <2>2. PhaseOrdering'
      \* phase' = "challenge", so only the "challenge" conjunct applies.
      \* r_scalar' = r_nonce; c_scalar' = c_scalar = 0 (UNCHANGED, by
      \* pre-state PhaseOrdering's "commit" conjunct); s_scalar' = 0.
      <3>1. c_scalar = 0                                  BY <2>a
      <3>2. s_scalar = 0                                  BY <2>a
      <3> QED  BY <2>b, <2>d, <2>e, <3>1, <3>2
    <2>3. RIsCommitted'
      \* phase' = "challenge"; need R_point' = ScalarMult[<<r_scalar', G>>].
      \* r_scalar' = r_nonce, R_point' = ScalarMult[<<r_nonce, G>>]. Equal.
      BY <2>b, <2>c, <2>d
    <2>4. ChallengeFromValues'
      \* phase' = "challenge"; antecedent of ChallengeFromValues is
      \* phase' \in {"response","done"} which is false.
      BY <2>d
    <2>5. ResponseFromValues'
      \* phase' = "challenge"; antecedent false.
      BY <2>d
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>B. CASE ChallengeStep
    <2>a. phase = "challenge"                             BY <1>B DEF ChallengeStep
    <2>b. c_scalar' = Hash[<<R_point, A, M_hash>>]        BY <1>B DEF ChallengeStep
    <2>c. phase' = "response"                             BY <1>B DEF ChallengeStep
    <2>d. UNCHANGED <<r_scalar, R_point, s_scalar>>       BY <1>B DEF ChallengeStep
    <2>e. R_point \in GroupElement                        OBVIOUS
    <2>f. A \in GroupElement                              BY AType
    <2>g. M_hash \in GroupElement                         BY M_hashType
    <2>h. <<R_point, A, M_hash>> \in GroupElement \X GroupElement \X GroupElement
                                                          BY <2>e, <2>f, <2>g
    <2>i. c_scalar' \in ScalarValue                       BY <2>b, <2>h, HashType
    <2>j. r_scalar' = r_nonce
      \* From pre PhaseOrdering at "challenge".
      BY <2>a, <2>d
    <2>k. s_scalar' = 0
      \* From pre PhaseOrdering at "challenge".
      BY <2>a, <2>d
    <2>1. TypeInvariant'
      BY <2>c, <2>d, <2>i, <2>j, r_nonceType
    <2>2. PhaseOrdering'
      \* phase' = "response". Need:
      \*   r_scalar' = r_nonce  — from <2>j
      \*   c_scalar' = Hash[<<R_point', A, M_hash>>]  — by <2>b and <2>d
      \*   s_scalar' = 0  — from <2>k
      <3>1. R_point' = R_point                            BY <2>d
      <3>2. c_scalar' = Hash[<<R_point', A, M_hash>>]     BY <2>b, <3>1
      <3> QED  BY <2>c, <2>j, <2>k, <3>2
    <2>3. RIsCommitted'
      \* phase' = "response"; need R_point' = ScalarMult[<<r_scalar', G>>].
      \* R_point' = R_point (UNCHANGED).
      \* Pre-state RIsCommitted at "challenge": R_point = ScalarMult[<<r_scalar, G>>].
      \* r_scalar' = r_scalar (UNCHANGED).
      <3>1. R_point = ScalarMult[<<r_scalar, G>>]         BY <2>a
      <3>2. R_point' = R_point                            BY <2>d
      <3>3. r_scalar' = r_scalar                          BY <2>d
      <3> QED  BY <2>c, <3>1, <3>2, <3>3
    <2>4. ChallengeFromValues'
      \* phase' = "response"; need c_scalar' = Hash[<<R_point', A, M_hash>>].
      <3>1. R_point' = R_point                            BY <2>d
      <3>2. c_scalar' = Hash[<<R_point', A, M_hash>>]     BY <2>b, <3>1
      <3> QED  BY <2>c, <3>2
    <2>5. ResponseFromValues'
      \* phase' = "response"; antecedent (phase = "done") false.
      BY <2>c
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>C. CASE ResponseStep
    <2>a. phase = "response"                              BY <1>C DEF ResponseStep
    <2>b. s_scalar' = ScalarAdd(r_scalar, ScalarMul(c_scalar, a_secret))
                                                          BY <1>C DEF ResponseStep
    <2>c. phase' = "done"                                 BY <1>C DEF ResponseStep
    <2>d. UNCHANGED <<r_scalar, R_point, c_scalar>>       BY <1>C DEF ResponseStep
    <2>e. r_scalar \in ScalarValue                        OBVIOUS
    <2>f. c_scalar \in ScalarValue                        OBVIOUS
    <2>g. a_secret \in ScalarValue                        BY a_secretType
    <2>h. ScalarMul(c_scalar, a_secret) \in ScalarValue   BY <2>f, <2>g, ScalarMulType
    <2>i. s_scalar' \in ScalarValue                       BY <2>b, <2>e, <2>h, ScalarAddType
    <2>j. r_scalar' = r_nonce
      \* From pre PhaseOrdering at "response".
      BY <2>a, <2>d
    <2>k. c_scalar' = Hash[<<R_point, A, M_hash>>]
      \* From pre PhaseOrdering at "response".
      BY <2>a, <2>d
    <2>1. TypeInvariant'
      BY <2>c, <2>d, <2>i, <2>j, r_nonceType
    <2>2. PhaseOrdering'
      \* phase' = "done". Need r_scalar' = r_nonce and
      \* s_scalar' = ScalarAdd(r_scalar', ScalarMul(c_scalar', a_secret)).
      <3>1. r_scalar' = r_scalar                          BY <2>d
      <3>2. c_scalar' = c_scalar                          BY <2>d
      <3>3. s_scalar' = ScalarAdd(r_scalar', ScalarMul(c_scalar', a_secret))
        BY <2>b, <3>1, <3>2
      <3> QED  BY <2>c, <2>j, <3>3
    <2>3. RIsCommitted'
      \* phase' = "done"; need R_point' = ScalarMult[<<r_scalar', G>>].
      <3>1. R_point = ScalarMult[<<r_scalar, G>>]         BY <2>a
      <3>2. R_point' = R_point                            BY <2>d
      <3>3. r_scalar' = r_scalar                          BY <2>d
      <3> QED  BY <2>c, <3>1, <3>2, <3>3
    <2>4. ChallengeFromValues'
      \* phase' = "done"; need c_scalar' = Hash[<<R_point', A, M_hash>>].
      <3>1. c_scalar = Hash[<<R_point, A, M_hash>>]       BY <2>a
      <3>2. R_point' = R_point                            BY <2>d
      <3>3. c_scalar' = c_scalar                          BY <2>d
      <3> QED  BY <2>c, <3>1, <3>2, <3>3
    <2>5. ResponseFromValues'
      \* phase' = "done"; need s_scalar' = ScalarAdd(...).
      <3>1. r_scalar' = r_scalar                          BY <2>d
      <3>2. c_scalar' = c_scalar                          BY <2>d
      <3> QED  BY <2>b, <2>c, <3>1, <3>2
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>D. CASE Done
    BY <1>D DEF Done, vars
  <1>E. CASE Next
    BY <1>E, <1>A, <1>B, <1>C, <1>D DEF Next
  <1> QED  BY <1>0, <1>E

(*-------------------------------------------------------------------------*)
(* Main safety theorem.                                                    *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* Per-invariant corollaries.                                              *)
(*-------------------------------------------------------------------------*)
THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM PhaseOrderingSafety == Spec => []PhaseOrdering
  BY Safety, PTL DEF Inv

THEOREM RIsCommittedSafety == Spec => []RIsCommitted
  BY Safety, PTL DEF Inv

THEOREM ChallengeFromValuesSafety == Spec => []ChallengeFromValues
  BY Safety, PTL DEF Inv

THEOREM ResponseFromValuesSafety == Spec => []ResponseFromValues
  BY Safety, PTL DEF Inv

====
