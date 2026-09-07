---- MODULE StreamGraphFanout_Proof ----
(* Parametric proof for the bounded one-source/two-sink fan-out profile.
   Safety is independent of scheduling. EventualDrain uses exactly the weak
   fairness premise declared by StreamGraphFanout.Spec. *)
EXTENDS StreamGraphFanout, Naturals, Sequences, SequenceTheorems,
        NaturalsInduction, TLAPS

Inv == TypeInvariant /\ BackpressureCorrect /\ PerBranchConservation

LEMMA SourceBalance ==
  ASSUME NEW i \in Nat, NEW q \in Nat, NEW e \in Nat, i = q + e
  PROVE  i + 1 = (q + 1) + e
  BY SMT

LEMMA ConsumeBalance ==
  ASSUME NEW i \in Nat, NEW q \in Nat, NEW qp \in Nat, NEW e \in Nat,
         i = q + e, qp + 1 = q
  PROVE  i = qp + (e + 1)
  BY SMT

LEMMA PositiveQueueLeavesEmissionRoom ==
  ASSUME NEW i \in Nat, NEW q \in Nat, NEW e \in Nat, NEW m \in Nat,
         i = q + e, q > 0, i <= m
  PROVE  e < m
  BY SMT

LEMMA TailWithinCapacity ==
  ASSUME NEW q \in Nat, NEW qp \in Nat, NEW cap \in Nat,
         qp + 1 = q, q <= cap
  PROVE  qp <= cap
  BY SMT

LEMMA DecrementToPredecessor ==
  ASSUME NEW before \in Nat, NEW after \in Nat, NEW n \in Nat,
         before = n, after + 1 = before, n > 0
  PROVE  after = n - 1
  BY SMT

LEMMA IncrementDecreasesComplement ==
  ASSUME NEW m \in Nat, NEW before \in Nat, before < m
  PROVE  (m - (before + 1)) + 1 = m - before
  BY SMT

LEMMA BoundedComplementNat ==
  ASSUME NEW m \in Nat, NEW value \in Nat, value <= m
  PROVE  m - value \in Nat
  BY SMT

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY MaxInputsType DEF Init, TypeInvariant
  <1>2. BackpressureCorrect
    BY CapacityType DEF Init, BackpressureCorrect
  <1>3. PerBranchConservation
    BY DEF Init, PerBranchConservation
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BackpressureCorrect,
              PerBranchConservation
  <1>t. /\ left_queue \in Seq(RecordDomain)
         /\ right_queue \in Seq(RecordDomain)
         /\ ingested \in 0..MaxInputs
         /\ left_emitted \in 0..MaxInputs
         /\ right_emitted \in 0..MaxInputs
    BY DEF Inv, TypeInvariant
  <1>lens. /\ Len(left_queue) \in Nat /\ Len(right_queue) \in Nat
    BY <1>t
  <1>nat. /\ ingested \in Nat /\ left_emitted \in Nat
           /\ right_emitted \in Nat
    BY <1>t, MaxInputsType
  <1>bounds. /\ Len(left_queue) <= Capacity
              /\ Len(right_queue) <= Capacity
    BY DEF Inv, BackpressureCorrect
  <1>balance. /\ ingested = Len(left_queue) + left_emitted
               /\ ingested = Len(right_queue) + right_emitted
    BY DEF Inv, PerBranchConservation
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars

  <1>S. CASE SourceIngest
    <2> USE <1>S DEF SourceIngest
    <2> PICK v \in RecordDomain :
          /\ left_queue' = Append(left_queue, v)
          /\ right_queue' = Append(right_queue, v)
      BY <1>S DEF SourceIngest
    <2>c. /\ ingested' = ingested + 1
           /\ left_emitted' = left_emitted
           /\ right_emitted' = right_emitted
      BY DEF vars
    <2>room. /\ Len(left_queue) < Capacity
              /\ Len(right_queue) < Capacity
      BY <1>S DEF SourceIngest
    <2>1. TypeInvariant'
      BY <1>S, <2>c, MaxInputsType DEF SourceIngest, TypeInvariant
    <2>2. BackpressureCorrect'
      BY <2>room, CapacityType DEF BackpressureCorrect
    <2>3. PerBranchConservation'
      BY <1>lens, <1>nat, <1>balance, <2>c, SourceBalance
        DEF PerBranchConservation
    <2> QED  BY <2>1, <2>2, <2>3 DEF Inv

  <1>L. CASE ConsumeLeft
    <2>c. /\ left_queue' = Tail(left_queue)
           /\ left_emitted' = left_emitted + 1
           /\ right_queue' = right_queue
           /\ ingested' = ingested
           /\ right_emitted' = right_emitted
      BY <1>L DEF ConsumeLeft, vars
    <2>positive. Len(left_queue) > 0  BY <1>L DEF ConsumeLeft
    <2>tail. /\ left_queue' \in Seq(RecordDomain)
              /\ Len(left_queue') + 1 = Len(left_queue)
      BY <1>t, <2>c, <2>positive
    <2>emitroom. left_emitted < MaxInputs
      BY <1>lens, <1>nat, <1>balance, <2>positive, MaxInputsType,
         PositiveQueueLeavesEmissionRoom
    <2>1. TypeInvariant'
      BY <1>t, <2>c, <2>tail, <2>emitroom, MaxInputsType
        DEF TypeInvariant
    <2>2. BackpressureCorrect'
      BY <1>bounds, <1>lens, <2>c, <2>tail, CapacityType,
         TailWithinCapacity DEF BackpressureCorrect
    <2>3. PerBranchConservation'
      BY <1>lens, <1>nat, <1>balance, <2>c, <2>tail, ConsumeBalance
        DEF PerBranchConservation
    <2> QED  BY <2>1, <2>2, <2>3 DEF Inv

  <1>R. CASE ConsumeRight
    <2>c. /\ right_queue' = Tail(right_queue)
           /\ right_emitted' = right_emitted + 1
           /\ left_queue' = left_queue
           /\ ingested' = ingested
           /\ left_emitted' = left_emitted
      BY <1>R DEF ConsumeRight, vars
    <2>positive. Len(right_queue) > 0  BY <1>R DEF ConsumeRight
    <2>tail. /\ right_queue' \in Seq(RecordDomain)
              /\ Len(right_queue') + 1 = Len(right_queue)
      BY <1>t, <2>c, <2>positive
    <2>emitroom. right_emitted < MaxInputs
      BY <1>lens, <1>nat, <1>balance, <2>positive, MaxInputsType,
         PositiveQueueLeavesEmissionRoom
    <2>1. TypeInvariant'
      BY <1>t, <2>c, <2>tail, <2>emitroom, MaxInputsType
        DEF TypeInvariant
    <2>2. BackpressureCorrect'
      BY <1>bounds, <1>lens, <2>c, <2>tail, CapacityType,
         TailWithinCapacity DEF BackpressureCorrect
    <2>3. PerBranchConservation'
      BY <1>lens, <1>nat, <1>balance, <2>c, <2>tail, ConsumeBalance
        DEF PerBranchConservation
    <2> QED  BY <2>1, <2>2, <2>3 DEF Inv

  <1>D. CASE DoneStuttering
    BY <1>D DEF DoneStuttering, vars
  <1>X. CASE Next
    BY <1>X, <1>S, <1>L, <1>R, <1>D DEF Next, Work, Drain
  <1> QED  BY <1>0, <1>X

LEMMA WorkInv == Inv /\ Work => Inv'
  BY NextInv DEF Next, vars

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM BackpressureSafety == Spec => []BackpressureCorrect
  BY Safety, PTL DEF Inv

THEOREM PerBranchConservationSafety == Spec => []PerBranchConservation
  BY Safety, PTL DEF Inv

LEMMA CopyConservationDerived == Inv => CopyConservation
  BY SMT DEF Inv, TypeInvariant, PerBranchConservation, CopyConservation

THEOREM CopyConservationSafety == Spec => []CopyConservation
  BY Safety, CopyConservationDerived, PTL

LEMMA InvImpliesEnabled == Inv => SomeActionEnabled
  <1> SUFFICES ASSUME Inv PROVE SomeActionEnabled  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BackpressureCorrect
  <1>L. CASE Len(left_queue) > 0
    BY <1>L DEF SomeActionEnabled
  <1>R. CASE Len(right_queue) > 0
    BY <1>R DEF SomeActionEnabled
  <1>E. CASE Len(left_queue) = 0 /\ Len(right_queue) = 0
    <2>I. CASE ingested < MaxInputs
      <3>1. /\ Len(left_queue) < Capacity
              /\ Len(right_queue) < Capacity
        BY <1>E, CapacityType
      <3> QED  BY <2>I, <3>1 DEF SomeActionEnabled
    <2>D. CASE ~(ingested < MaxInputs)
      <3>1. ingested = MaxInputs
        BY <2>D, MaxInputsType DEF TypeInvariant
      <3> QED  BY <1>E, <3>1 DEF SomeActionEnabled,
                                      Terminal
    <2> QED  BY <2>I, <2>D
  <1> QED  BY <1>L, <1>R, <1>E

THEOREM SomeActionEnabledSafety == Spec => []SomeActionEnabled
  BY Safety, InvImpliesEnabled, PTL

THEOREM DeadlockFreedomSafety == Spec => []DeadlockFreedom
  BY SomeActionEnabledSafety, PTL DEF DeadlockFreedom

LEMMA WorkRemainingNat == Inv => WorkRemaining \in Nat
  BY MaxInputsType DEF Inv, TypeInvariant, WorkRemaining

LEMMA WorkDecreases ==
  Inv /\ Work => WorkRemaining' + 1 = WorkRemaining
  <1> SUFFICES ASSUME Inv, Work
               PROVE  WorkRemaining' + 1 = WorkRemaining  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, PerBranchConservation
  <1>t. /\ left_queue \in Seq(RecordDomain)
         /\ right_queue \in Seq(RecordDomain)
         /\ ingested \in 0..MaxInputs
         /\ left_emitted \in 0..MaxInputs
         /\ right_emitted \in 0..MaxInputs
    BY DEF Inv, TypeInvariant
  <1>balance. /\ ingested = Len(left_queue) + left_emitted
               /\ ingested = Len(right_queue) + right_emitted
    BY DEF Inv, PerBranchConservation
  <1>S. CASE SourceIngest
    <2>c. /\ ingested' = ingested + 1
           /\ left_emitted' = left_emitted
           /\ right_emitted' = right_emitted
      BY <1>S DEF SourceIngest, vars
    <2>dec. (MaxInputs - ingested') + 1 = MaxInputs - ingested
      BY <1>t, <2>c, MaxInputsType, IncrementDecreasesComplement
    <2>rank. (MaxInputs - ingested') +
              (MaxInputs - left_emitted') +
              (MaxInputs - right_emitted') + 1 =
              (MaxInputs - ingested) +
              (MaxInputs - left_emitted) +
              (MaxInputs - right_emitted)
      BY <1>t, <2>c, <2>dec, MaxInputsType, SMT
    <2> QED  BY <2>rank DEF WorkRemaining
  <1>L. CASE ConsumeLeft
    <2> USE <1>L DEF ConsumeLeft
    <2>c. /\ left_queue' = Tail(left_queue)
           /\ right_queue' = right_queue
           /\ ingested' = ingested
      BY DEF vars
    <2>positive. Len(left_queue) > 0  OBVIOUS
    <2>room. left_emitted < MaxInputs
      BY <1>t, <1>balance, <2>positive, MaxInputsType,
         PositiveQueueLeavesEmissionRoom
    <2>dec. (MaxInputs - left_emitted') + 1 =
              MaxInputs - left_emitted
      BY <1>t, <2>c, <2>room, MaxInputsType,
         IncrementDecreasesComplement
    <2>rank. (MaxInputs - ingested') +
              (MaxInputs - left_emitted') +
              (MaxInputs - right_emitted') + 1 =
              (MaxInputs - ingested) +
              (MaxInputs - left_emitted) +
              (MaxInputs - right_emitted)
      BY <1>t, <2>c, <2>dec, MaxInputsType, SMT
    <2> QED  BY <2>rank DEF WorkRemaining
  <1>R. CASE ConsumeRight
    <2> USE <1>R DEF ConsumeRight
    <2>c. /\ right_queue' = Tail(right_queue)
           /\ left_queue' = left_queue
           /\ ingested' = ingested
      BY DEF vars
    <2>positive. Len(right_queue) > 0  OBVIOUS
    <2>room. right_emitted < MaxInputs
      BY <1>t, <1>balance, <2>positive, MaxInputsType,
         PositiveQueueLeavesEmissionRoom
    <2>dec. (MaxInputs - right_emitted') + 1 =
              MaxInputs - right_emitted
      BY <1>t, <2>c, <2>room, MaxInputsType,
         IncrementDecreasesComplement
    <2>rank. (MaxInputs - ingested') +
              (MaxInputs - left_emitted') +
              (MaxInputs - right_emitted') + 1 =
              (MaxInputs - ingested) +
              (MaxInputs - left_emitted) +
              (MaxInputs - right_emitted)
      BY <1>t, <2>c, <2>dec, MaxInputsType, SMT
    <2> QED  BY <2>rank DEF WorkRemaining
  <1> QED  BY <1>S, <1>L, <1>R DEF Work, Drain

LEMMA ZeroWorkIsTerminal == Inv /\ WorkRemaining = 0 => Terminal
  <1> SUFFICES ASSUME Inv, WorkRemaining = 0 PROVE Terminal  OBVIOUS
  <1>t. /\ left_queue \in Seq(RecordDomain)
         /\ right_queue \in Seq(RecordDomain)
         /\ ingested \in 0..MaxInputs
         /\ left_emitted \in 0..MaxInputs
         /\ right_emitted \in 0..MaxInputs
    BY DEF Inv, TypeInvariant
  <1>balance. /\ ingested = Len(left_queue) + left_emitted
               /\ ingested = Len(right_queue) + right_emitted
    BY DEF Inv, PerBranchConservation
  <1>nat. /\ MaxInputs - ingested \in Nat
           /\ MaxInputs - left_emitted \in Nat
           /\ MaxInputs - right_emitted \in Nat
    BY <1>t, MaxInputsType
  <1>zero. /\ MaxInputs - ingested = 0
            /\ MaxInputs - left_emitted = 0
            /\ MaxInputs - right_emitted = 0
    BY <1>nat, SMT DEF WorkRemaining
  <1>counters. /\ ingested = MaxInputs
                 /\ left_emitted = MaxInputs
                 /\ right_emitted = MaxInputs
    BY <1>t, <1>zero, MaxInputsType, SMT
  <1>lens. /\ Len(left_queue) \in Nat /\ Len(right_queue) \in Nat
    BY DEF Inv, TypeInvariant
  <1>empty. /\ Len(left_queue) = 0 /\ Len(right_queue) = 0
    BY <1>balance, <1>counters, <1>lens, MaxInputsType, SMT
  <1> QED  BY <1>counters, <1>empty DEF Terminal

LEMMA FairRecordType == FairRecord \in RecordDomain
  BY RecordDomainNonEmpty DEF FairRecord

LEMMA NonterminalEnablesFairWork ==
  Inv /\ ~Terminal => ENABLED <<FairWork>>_vars
  <1> SUFFICES ASSUME Inv, ~Terminal PROVE ENABLED <<FairWork>>_vars  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BackpressureCorrect
  <1>t. /\ left_queue \in Seq(RecordDomain)
         /\ right_queue \in Seq(RecordDomain)
         /\ ingested \in 0..MaxInputs
         /\ left_emitted \in 0..MaxInputs
         /\ right_emitted \in 0..MaxInputs
    BY DEF Inv, TypeInvariant
  <1>workeq. <<FairWork>>_vars <=>
          <<FairSourceIngest>>_vars \/ <<Drain>>_vars
    BY DEF FairWork, vars
  <1>workdist. ENABLED <<FairWork>>_vars <=>
          ENABLED <<FairSourceIngest>>_vars \/ ENABLED <<Drain>>_vars
    <2>1. ENABLED <<FairWork>>_vars <=>
            ENABLED (<<FairSourceIngest>>_vars \/ <<Drain>>_vars)
      BY <1>workeq, ENABLEDrules
    <2>2. ENABLED (<<FairSourceIngest>>_vars \/ <<Drain>>_vars) <=>
            ENABLED <<FairSourceIngest>>_vars \/ ENABLED <<Drain>>_vars
      BY ENABLEDaxioms
    <2> QED  BY <2>1, <2>2
  <1>draineq. <<Drain>>_vars <=>
          <<ConsumeLeft>>_vars \/ <<ConsumeRight>>_vars
    BY DEF Drain, vars
  <1>draindist. ENABLED <<Drain>>_vars <=>
          ENABLED <<ConsumeLeft>>_vars \/ ENABLED <<ConsumeRight>>_vars
    <2>1. ENABLED <<Drain>>_vars <=>
            ENABLED (<<ConsumeLeft>>_vars \/ <<ConsumeRight>>_vars)
      BY <1>draineq, ENABLEDrules
    <2>2. ENABLED (<<ConsumeLeft>>_vars \/ <<ConsumeRight>>_vars) <=>
            ENABLED <<ConsumeLeft>>_vars \/ ENABLED <<ConsumeRight>>_vars
      BY ENABLEDaxioms
    <2> QED  BY <2>1, <2>2
  <1>L. CASE Len(left_queue) > 0
    <2>change. Tail(left_queue) # left_queue
      BY <1>L, <1>t
    <2>1. ENABLED <<ConsumeLeft>>_vars
      BY <1>L, <1>t, <2>change, ExpandENABLED
        DEF ConsumeLeft, vars
    <2>2. ENABLED <<Drain>>_vars  BY <2>1, <1>draindist
    <2> QED  BY <2>2, <1>workdist
  <1>R. CASE Len(right_queue) > 0
    <2>change. Tail(right_queue) # right_queue
      BY <1>R, <1>t
    <2>1. ENABLED <<ConsumeRight>>_vars
      BY <1>R, <1>t, <2>change, ExpandENABLED
        DEF ConsumeRight, vars
    <2>2. ENABLED <<Drain>>_vars  BY <2>1, <1>draindist
    <2> QED  BY <2>2, <1>workdist
  <1>E. CASE Len(left_queue) = 0 /\ Len(right_queue) = 0
    <2>1. ingested < MaxInputs
      BY <1>E, MaxInputsType DEF Terminal, TypeInvariant
    <2>2. /\ Len(left_queue) < Capacity
            /\ Len(right_queue) < Capacity
      BY <1>E, CapacityType
    <2>change. Append(left_queue, FairRecord) # left_queue
      BY <1>t, FairRecordType
    <2>3. ENABLED <<FairSourceIngest>>_vars
      BY <1>t, <2>1, <2>2, <2>change, FairRecordType,
         ExpandENABLED DEF FairSourceIngest, vars
    <2> QED  BY <2>3, <1>workdist
  <1> QED  BY <1>L, <1>R, <1>E

THEOREM EventualDrainProved == Spec => EventualDrain
PROOF
  <1> DEFINE P(m) == Spec => <>(Terminal \/ WorkRemaining = m)
  <1> HIDE DEF P
  <1>base. P(3 * MaxInputs)
    <2> SUFFICES ASSUME Spec
                 PROVE  <>(Terminal \/ WorkRemaining = 3 * MaxInputs)
      BY DEF P
    <2>1. Init => WorkRemaining = 3 * MaxInputs
      BY MaxInputsType DEF Init, WorkRemaining
    <2> QED  BY <2>1, PTL DEF Spec
  <1>step. \A n \in 1 .. (3 * MaxInputs) : P(n) => P(n - 1)
    <2> SUFFICES ASSUME NEW n \in 1 .. (3 * MaxInputs)
                 PROVE  Spec /\ <>(Terminal \/ WorkRemaining = n)
                          => <>(Terminal \/ WorkRemaining = (n - 1))
      BY DEF P
    <2>i. Inv /\ (Terminal \/ WorkRemaining = n) /\ [Next]_vars
            => \/ Terminal'
               \/ (WorkRemaining = n)'
               \/ (WorkRemaining = (n - 1))'
      <3> SUFFICES ASSUME Inv, (Terminal \/ WorkRemaining = n), [Next]_vars
                   PROVE  \/ Terminal'
                          \/ (WorkRemaining = n)'
                          \/ (WorkRemaining = (n - 1))'
        OBVIOUS
      <3>0. CASE UNCHANGED vars
        BY <3>0 DEF vars, Terminal, WorkRemaining
      <3>W. CASE Work
        <4>nt. ~Terminal
          BY <3>W DEF Work, Drain, SourceIngest, ConsumeLeft, ConsumeRight,
                              Terminal
        <4>cur. WorkRemaining = n  BY <4>nt
        <4>dec. WorkRemaining' + 1 = WorkRemaining
          BY <3>W, WorkDecreases
        <4>invp. Inv'  BY <3>W, WorkInv
        <4>natp. WorkRemaining' \in Nat
          <5>t. /\ ingested' \in 0..MaxInputs
                  /\ left_emitted' \in 0..MaxInputs
                  /\ right_emitted' \in 0..MaxInputs
            BY <4>invp DEF Inv, TypeInvariant
          <5>bounds. /\ ingested' \in Nat /\ ingested' <= MaxInputs
                      /\ left_emitted' \in Nat
                      /\ left_emitted' <= MaxInputs
                      /\ right_emitted' \in Nat
                      /\ right_emitted' <= MaxInputs
            BY <5>t, MaxInputsType
          <5>a. MaxInputs - ingested' \in Nat
            BY <5>bounds, MaxInputsType, BoundedComplementNat
          <5>b. MaxInputs - left_emitted' \in Nat
            BY <5>bounds, MaxInputsType, BoundedComplementNat
          <5>c. MaxInputs - right_emitted' \in Nat
            BY <5>bounds, MaxInputsType, BoundedComplementNat
          <5> QED  BY <5>a, <5>b, <5>c DEF WorkRemaining
        <4> QED
          BY <4>cur, <4>dec, <4>natp, WorkRemainingNat, MaxInputsType,
             DecrementToPredecessor
      <3>D. CASE DoneStuttering
        BY <3>D DEF DoneStuttering, vars, Terminal
      <3>X. CASE Next
        BY <3>X, <3>W, <3>D DEF Next
      <3> QED  BY <3>0, <3>X
    <2>ii. Inv /\ (Terminal \/ WorkRemaining = n)
             /\ <<Next>>_vars /\ FairWork
             => Terminal' \/ (WorkRemaining = (n - 1))'
      <3> SUFFICES ASSUME Inv, (Terminal \/ WorkRemaining = n),
                          <<Next>>_vars, FairWork
                   PROVE  Terminal' \/ (WorkRemaining = (n - 1))'
        OBVIOUS
      <3>w. Work
        BY FairRecordType DEF FairWork, FairSourceIngest, Work, SourceIngest,
                                   Drain
      <3>nt. ~Terminal
        BY <3>w DEF Work, Drain, SourceIngest, ConsumeLeft, ConsumeRight,
                       Terminal
      <3>cur. WorkRemaining = n  BY <3>nt
      <3>dec. WorkRemaining' + 1 = WorkRemaining
        BY <3>w, WorkDecreases
      <3>invp. Inv'  BY <3>w, WorkInv
      <3>natp. WorkRemaining' \in Nat
        <4>t. /\ ingested' \in 0..MaxInputs
                /\ left_emitted' \in 0..MaxInputs
                /\ right_emitted' \in 0..MaxInputs
          BY <3>invp DEF Inv, TypeInvariant
        <4>bounds. /\ ingested' \in Nat /\ ingested' <= MaxInputs
                    /\ left_emitted' \in Nat
                    /\ left_emitted' <= MaxInputs
                    /\ right_emitted' \in Nat
                    /\ right_emitted' <= MaxInputs
          BY <4>t, MaxInputsType
        <4>a. MaxInputs - ingested' \in Nat
          BY <4>bounds, MaxInputsType, BoundedComplementNat
        <4>b. MaxInputs - left_emitted' \in Nat
          BY <4>bounds, MaxInputsType, BoundedComplementNat
        <4>c. MaxInputs - right_emitted' \in Nat
          BY <4>bounds, MaxInputsType, BoundedComplementNat
        <4> QED  BY <4>a, <4>b, <4>c DEF WorkRemaining
      <3>pred. WorkRemaining' = n - 1
        BY <3>cur, <3>dec, <3>natp, WorkRemainingNat, MaxInputsType,
           DecrementToPredecessor
      <3> QED  BY <3>pred
    <2>iii. Inv /\ (Terminal \/ WorkRemaining = n) /\ ~Terminal
              => ENABLED <<FairWork>>_vars
      BY NonterminalEnablesFairWork
    <2> QED  BY <2>i, <2>ii, <2>iii, Safety, PTL DEF Spec, Fairness
  <1>dn. P(0)
    BY <1>base, <1>step, MaxInputsType, DownwardNatInduction
  <1>zero. Spec => [](WorkRemaining = 0 => Terminal)
    <2>1. Inv => (WorkRemaining = 0 => Terminal)
      BY ZeroWorkIsTerminal
    <2> QED  BY <2>1, Safety, PTL DEF Spec
  <1> QED  BY <1>dn, <1>zero, PTL DEF P, EventualDrain
====
