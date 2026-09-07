---- MODULE AuditSinkFromGlue_Proof ----
(***************************************************************************
  Parametric TLAPS proof of the AuditSink pure-glue refinement:

      Refinement == Spec => AS!Spec

  Under the substitution, Init, Next, and vars are the AuditSink target with
  renamed variables. MaxLogLen and Hash typing are used for the construction
  TypeInvariant; HashCR is not required because this module states no
  cryptographic tamper-evidence theorem. The proof does not show that a retained
  component supplies the three chain obligations; their state remains glue.
 ***************************************************************************)
EXTENDS AuditSinkFromGlue, TLAPS

ASSUME MaxLogLenType == MaxLogLen \in Nat
ASSUME HashType == \A p \in Nat, op \in Operations : Hash(p, op) \in Nat

\* Shape of a chain entry, matching the record constructed in Record(op).
ChainEntry == [operation : Operations, prev_hash : Nat, hash : Nat]

\* Inductive strengthening. TypeInvariant alone does not say `chain` is a
\* sequence, and the length arithmetic under Append needs that.
Inv ==
    /\ chain \in Seq(ChainEntry)
    /\ carry \in Nat
    /\ Len(chain) <= MaxLogLen

(*-------------------------------------------------------------------------*)
(* Safety of the construction's own (type) invariant.                      *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. chain \in Seq(ChainEntry)   BY DEF Init, ChainEntry
  <1>2. carry \in Nat               BY DEF Init
  <1>3. Len(chain) <= MaxLogLen     BY MaxLogLenType DEF Init
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, vars
  <1>X. CASE Next
    <2> SUFFICES ASSUME NEW op \in Operations, Record(op)
                 PROVE  Inv'
      BY <1>X DEF Next
    <2> DEFINE
      new_hash == Hash(carry, op)
      entry == [operation |-> op, prev_hash |-> carry, hash |-> new_hash]
    <2>a. chain' = Append(chain, entry) /\ carry' = new_hash
      BY DEF Record
    <2>b. Len(chain) < MaxLogLen
      BY DEF Record
    <2>c. chain \in Seq(ChainEntry) /\ carry \in Nat
      BY DEF Inv
    <2>d. new_hash \in Nat
      BY <2>c, HashType
    <2>e. entry \in ChainEntry
      BY <2>c, <2>d DEF ChainEntry
    <2>1. chain' \in Seq(ChainEntry)
      BY <2>a, <2>c, <2>e
    <2>2. carry' \in Nat
      BY <2>a, <2>d
    <2>3. Len(chain') <= MaxLogLen
      BY <2>a, <2>b, <2>c, MaxLogLenType
    <2> QED  BY <2>1, <2>2, <2>3 DEF Inv
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

\* TypeInvariant follows from the stronger sequence-typed invariant.
THEOREM TypeSafety == Spec => []TypeInvariant
  <1>1. Inv => TypeInvariant
    BY DEF Inv, TypeInvariant
  <1> QED  BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement. No invariant is carried into it and none is needed: the  *)
(* substitution is a relabelling, so each step below is the target's own    *)
(* definition read under the new variable names.                           *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => AS!Init
  BY DEF Init, AS!Init

LEMMA NextRefines == [Next]_vars => [AS!Next]_(AS!vars)
  <1> SUFFICES ASSUME [Next]_vars PROVE [AS!Next]_(AS!vars)
    OBVIOUS
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<chain, carry>>
      BY <1>0 DEF vars
    <2> QED  BY <2>1 DEF AS!vars
  <1>X. CASE Next
    <2> SUFFICES ASSUME NEW op \in Operations, Record(op)
                 PROVE  AS!Next
      BY <1>X DEF Next
    <2>1. AS!Record(op)
      BY DEF Record, AS!Record
    <2> QED  BY <2>1 DEF AS!Next
  <1> QED  BY <1>0, <1>X

(*-------------------------------------------------------------------------*)
(* The construction refines the AuditSink model by variable relabeling.    *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => AS!Spec
  <1>1. Init => AS!Init                                 BY InitRefines
  <1>2. [Next]_vars => [AS!Next]_(AS!vars)              BY NextRefines
  <1> QED  BY <1>1, <1>2, PTL DEF Spec, AS!Spec

\* Restatement in the construction module's public vocabulary.
THEOREM RefinementOriginal == Spec => AuditSinkRefinement
  BY Refinement DEF AuditSinkRefinement

====
