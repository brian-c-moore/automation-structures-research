---- MODULE StreamGraph_Proof ----
(* Carrier-level proof for the exact three- and four-node linear-chain boundary. *)
EXTENDS StreamGraph, Naturals, Sequences, SequenceTheorems, TLAPS

Inv == TypeInvariant /\ BackpressureCorrect /\ OccupancyCountConservation

(* Keep nonlinear sequence reasoning out of the arithmetic backend. These
   small lemmas are the complete counter/occupancy algebra used below. *)
LEMMA SourceArithmetic ==
  ASSUME NEW i \in Nat, NEW d \in Nat, NEW e \in Nat, i = d + e
  PROVE  i + 1 = (d + 1) + e
  BY SMT

LEMMA SinkArithmetic ==
  ASSUME NEW i \in Nat, NEW d \in Nat, NEW dp \in Nat, NEW e \in Nat,
         i = d + e, dp + 1 = d
  PROVE  i = dp + (e + 1)
  BY SMT

LEMMA PositiveDepthLeavesRoom ==
  ASSUME NEW i \in Nat, NEW d \in Nat, NEW e \in Nat, NEW m \in Nat,
         i = d + e, d > 0, i <= m
  PROVE  e < m
  BY SMT

LEMMA TailBound ==
  ASSUME NEW before \in Nat, NEW after \in Nat, NEW cap \in Nat,
         after + 1 = before, before <= cap
  PROVE  after <= cap
  BY SMT

LEMMA TwoQueueTail ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW bp \in Nat, bp + 1 = b
  PROVE  a + bp + 1 = a + b
  BY SMT

LEMMA ThreeQueueTail ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, NEW cp \in Nat,
         cp + 1 = c
  PROVE  a + b + cp + 1 = a + b + c
  BY SMT

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY MaxInputsType DEF Init, TypeInvariant
  <1>2. BackpressureCorrect
    BY CapacityType DEF Init, BackpressureCorrect
  <1>3. OccupancyCountConservation
    <2>A. CASE ChainLength = 3
      BY <2>A DEF Init, OccupancyCountConservation, QueueDepth
    <2>B. CASE ChainLength = 4
      BY <2>B DEF Init, OccupancyCountConservation, QueueDepth
    <2> QED  BY <2>A, <2>B, RetainedChainLength
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BackpressureCorrect,
              OccupancyCountConservation
  <1>t. /\ q1 \in Seq(RecordDomain) /\ q2 \in Seq(RecordDomain)
         /\ q3 \in Seq(RecordDomain)
         /\ (ChainLength = 3 => q3 = <<>>)
         /\ ingested \in 0..MaxInputs /\ emitted \in 0..MaxInputs
    BY DEF Inv, TypeInvariant
  <1>b. /\ Len(q1) <= Capacity /\ Len(q2) <= Capacity
         /\ (ChainLength = 4 => Len(q3) <= Capacity)
    BY DEF Inv, BackpressureCorrect
  <1>lens. /\ Len(q1) \in Nat /\ Len(q2) \in Nat /\ Len(q3) \in Nat
    BY <1>t
  <1>in. ingested \in Nat  BY <1>t, MaxInputsType
  <1>en. emitted \in Nat   BY <1>t, MaxInputsType
  <1>qd. QueueDepth \in Nat
    <2>A. CASE ChainLength = 3  BY <2>A, <1>lens DEF QueueDepth
    <2>B. CASE ChainLength = 4  BY <2>B, <1>lens DEF QueueDepth
    <2> QED  BY <2>A, <2>B, RetainedChainLength
  <1>nr. ingested = QueueDepth + emitted
    BY DEF Inv, OccupancyCountConservation
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars, QueueDepth

  <1>S. CASE SourceIngest
    <2> PICK v \in RecordDomain : q1' = Append(q1, v)
      BY <1>S DEF SourceIngest
    <2>c. /\ q2' = q2 /\ q3' = q3
           /\ ingested' = ingested + 1 /\ emitted' = emitted
      BY <1>S DEF SourceIngest, vars
    <2>r. Len(q1) < Capacity
      BY <1>S, CapacityType DEF SourceIngest, IsFull
    <2>1. TypeInvariant'
      BY <2>c, <1>S, MaxInputsType DEF SourceIngest, TypeInvariant
    <2>2. BackpressureCorrect'
      BY <2>c, <2>r, CapacityType DEF BackpressureCorrect
    <2>d. QueueDepth' = QueueDepth + 1
      <3>A. CASE ChainLength = 3
        BY <3>A, <2>c DEF QueueDepth
      <3>B. CASE ChainLength = 4
        BY <3>B, <2>c DEF QueueDepth
      <3> QED  BY <3>A, <3>B, RetainedChainLength
    <2>3. OccupancyCountConservation'
      BY <1>nr, <1>t, <1>qd, <2>c, <2>d, SourceArithmetic
        DEF OccupancyCountConservation
    <2> QED  BY <2>1, <2>2, <2>3 DEF Inv

  <1>M2. CASE Middle2Fire
    <2>c. /\ q1' = Tail(q1) /\ q2' = Append(q2, Head(q1))
           /\ q3' = q3 /\ ingested' = ingested /\ emitted' = emitted
      BY <1>M2 DEF Middle2Fire, vars
    <2>ne. ~IsEmpty(q1)  BY <1>M2 DEF Middle2Fire
    <2>r. Len(q2) < Capacity
      BY <1>M2, CapacityType DEF Middle2Fire, IsFull
    <2>1. TypeInvariant'
      BY <2>c, <2>ne DEF TypeInvariant, IsEmpty
    <2>2. BackpressureCorrect'
      BY <2>c, <2>ne, <2>r, CapacityType
        DEF BackpressureCorrect, IsEmpty
    <2>d. QueueDepth' = QueueDepth
      <3>A. CASE ChainLength = 3
        BY <3>A, <2>c, <2>ne DEF QueueDepth, IsEmpty
      <3>B. CASE ChainLength = 4
        BY <3>B, <2>c, <2>ne DEF QueueDepth, IsEmpty
      <3> QED  BY <3>A, <3>B, RetainedChainLength
    <2>3. OccupancyCountConservation'
      BY <2>c, <2>d DEF OccupancyCountConservation
    <2> QED  BY <2>1, <2>2, <2>3 DEF Inv

  <1>M3. CASE Middle3Fire
    <2>cl. ChainLength = 4  BY <1>M3 DEF Middle3Fire
    <2>c. /\ q1' = q1 /\ q2' = Tail(q2) /\ q3' = Append(q3, Head(q2))
           /\ ingested' = ingested /\ emitted' = emitted
      BY <1>M3 DEF Middle3Fire, vars
    <2>ne. ~IsEmpty(q2)  BY <1>M3 DEF Middle3Fire
    <2>r. Len(q3) < Capacity
      BY <1>M3, CapacityType DEF Middle3Fire, IsFull
    <2>1. TypeInvariant'
      BY <2>cl, <2>c, <2>ne DEF TypeInvariant, IsEmpty
    <2>2. BackpressureCorrect'
      BY <2>cl, <2>c, <2>ne, <2>r, CapacityType
        DEF BackpressureCorrect, IsEmpty
    <2>d. QueueDepth' = QueueDepth
      BY <2>cl, <2>c, <2>ne DEF QueueDepth, IsEmpty
    <2>3. OccupancyCountConservation'
      BY <2>c, <2>d DEF OccupancyCountConservation
    <2> QED  BY <2>1, <2>2, <2>3 DEF Inv

  <1>K3. CASE SinkConsume3
    <2>cl. ChainLength = 3  BY <1>K3 DEF SinkConsume3
    <2>c. /\ q1' = q1 /\ q2' = Tail(q2) /\ q3' = q3
           /\ ingested' = ingested /\ emitted' = emitted + 1
      BY <1>K3 DEF SinkConsume3, vars
    <2>ne. ~IsEmpty(q2)  BY <1>K3 DEF SinkConsume3
    <2>tail. /\ q2' \in Seq(RecordDomain)
              /\ Len(q2') + 1 = Len(q2)
      BY <2>c, <2>ne DEF IsEmpty
    <2>positive. QueueDepth > 0
      BY <1>lens, <2>cl, <2>ne DEF QueueDepth, IsEmpty
    <2>room. emitted < MaxInputs
      BY <1>nr, <1>t, <1>qd, <2>positive, MaxInputsType,
         PositiveDepthLeavesRoom
    <2>1. TypeInvariant'
      BY <2>cl, <2>c, <2>tail, <2>room, MaxInputsType DEF TypeInvariant
    <2>2. BackpressureCorrect'
      BY <1>b, <1>lens, <2>cl, <2>c, <2>tail, CapacityType,
         TailBound DEF BackpressureCorrect
    <2>d. QueueDepth' + 1 = QueueDepth
      BY <1>lens, <2>cl, <2>c, <2>tail, TwoQueueTail DEF QueueDepth
    <2>qdp. QueueDepth' \in Nat
      BY <1>t, <2>cl, <2>c, <2>tail DEF QueueDepth
    <2>balance. ingested = QueueDepth' + (emitted + 1)
      BY <1>nr, <1>in, <1>en, <1>qd, <2>d, <2>qdp, SinkArithmetic
    <2>3. OccupancyCountConservation'
      BY <2>c, <2>balance DEF OccupancyCountConservation
    <2> QED  BY <2>1, <2>2, <2>3 DEF Inv

  <1>K4. CASE SinkConsume4
    <2>cl. ChainLength = 4  BY <1>K4 DEF SinkConsume4
    <2>c. /\ q1' = q1 /\ q2' = q2 /\ q3' = Tail(q3)
           /\ ingested' = ingested /\ emitted' = emitted + 1
      BY <1>K4 DEF SinkConsume4, vars
    <2>ne. ~IsEmpty(q3)  BY <1>K4 DEF SinkConsume4
    <2>tail. /\ q3' \in Seq(RecordDomain)
              /\ Len(q3') + 1 = Len(q3)
      BY <2>c, <2>ne DEF IsEmpty
    <2>positive. QueueDepth > 0
      BY <1>lens, <2>cl, <2>ne DEF QueueDepth, IsEmpty
    <2>room. emitted < MaxInputs
      BY <1>nr, <1>t, <1>qd, <2>positive, MaxInputsType,
         PositiveDepthLeavesRoom
    <2>1. TypeInvariant'
      BY <2>cl, <2>c, <2>tail, <2>room, MaxInputsType DEF TypeInvariant
    <2>2. BackpressureCorrect'
      BY <1>b, <1>lens, <2>cl, <2>c, <2>tail, CapacityType,
         TailBound DEF BackpressureCorrect
    <2>d. QueueDepth' + 1 = QueueDepth
      BY <1>lens, <2>cl, <2>c, <2>tail, ThreeQueueTail DEF QueueDepth
    <2>qdp. QueueDepth' \in Nat
      BY <1>t, <2>cl, <2>c, <2>tail DEF QueueDepth
    <2>balance. ingested = QueueDepth' + (emitted + 1)
      BY <1>nr, <1>in, <1>en, <1>qd, <2>d, <2>qdp, SinkArithmetic
    <2>3. OccupancyCountConservation'
      BY <2>c, <2>balance DEF OccupancyCountConservation
    <2> QED  BY <2>1, <2>2, <2>3 DEF Inv

  <1>D. CASE DoneStuttering
    BY <1>D DEF DoneStuttering, vars, QueueDepth
  <1>X. CASE Next
    BY <1>X, <1>S, <1>M2, <1>M3, <1>K3, <1>K4, <1>D DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv
THEOREM BackpressureSafety == Spec => []BackpressureCorrect
  BY Safety, PTL DEF Inv
THEOREM OccupancyCountConservationSafety == Spec => []OccupancyCountConservation
  BY Safety, PTL DEF Inv

THEOREM NoRecordLossSafety == Spec => []NoRecordLoss
  BY OccupancyCountConservationSafety, PTL DEF NoRecordLoss

LEMMA InvImpliesEnabled == Inv => SomeActionEnabled
  <1> SUFFICES ASSUME Inv PROVE SomeActionEnabled  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BackpressureCorrect
  <1>A. CASE ChainLength = 3
    <2>S. CASE ~IsEmpty(q2)
      BY <1>A, <2>S DEF SomeActionEnabled
    <2>M. CASE IsEmpty(q2) /\ ~IsEmpty(q1)
      <3>1. ~IsFull(q2)  BY <2>M, CapacityType DEF IsEmpty, IsFull
      <3> QED  BY <2>M, <3>1 DEF SomeActionEnabled
    <2>E. CASE IsEmpty(q2) /\ IsEmpty(q1)
      <3>I. CASE ingested < MaxInputs
        <4>1. ~IsFull(q1)  BY <2>E, CapacityType DEF IsEmpty, IsFull
        <4> QED  BY <3>I, <4>1 DEF SomeActionEnabled
      <3>D. CASE ~(ingested < MaxInputs)
        <4>1. ingested = MaxInputs  BY <3>D, MaxInputsType
        <4>2. IsEmpty(q3)  BY <1>A DEF IsEmpty
        <4> QED  BY <4>1, <4>2, <2>E, <1>A DEF SomeActionEnabled
      <3> QED  BY <3>I, <3>D
    <2> QED  BY <2>S, <2>M, <2>E DEF IsEmpty
  <1>B. CASE ChainLength = 4
    <2>S. CASE ~IsEmpty(q3)
      BY <1>B, <2>S DEF SomeActionEnabled
    <2>M3. CASE IsEmpty(q3) /\ ~IsEmpty(q2)
      <3>1. ~IsFull(q3)  BY <2>M3, CapacityType DEF IsEmpty, IsFull
      <3> QED  BY <1>B, <2>M3, <3>1 DEF SomeActionEnabled
    <2>M2. CASE IsEmpty(q3) /\ IsEmpty(q2) /\ ~IsEmpty(q1)
      <3>1. ~IsFull(q2)  BY <2>M2, CapacityType DEF IsEmpty, IsFull
      <3> QED  BY <2>M2, <3>1 DEF SomeActionEnabled
    <2>E. CASE IsEmpty(q3) /\ IsEmpty(q2) /\ IsEmpty(q1)
      <3>I. CASE ingested < MaxInputs
        <4>1. ~IsFull(q1)  BY <2>E, CapacityType DEF IsEmpty, IsFull
        <4> QED  BY <3>I, <4>1 DEF SomeActionEnabled
      <3>D. CASE ~(ingested < MaxInputs)
        <4>1. ingested = MaxInputs  BY <3>D, MaxInputsType
        <4> QED  BY <4>1, <2>E, <1>B DEF SomeActionEnabled
      <3> QED  BY <3>I, <3>D
    <2> QED  BY <2>S, <2>M3, <2>M2, <2>E DEF IsEmpty
  <1> QED  BY <1>A, <1>B, RetainedChainLength

THEOREM SomeActionEnabledSafety == Spec => []SomeActionEnabled
  <1> QED  BY Safety, InvImpliesEnabled, PTL

THEOREM DeadlockFreedomSafety == Spec => []DeadlockFreedom
  BY SomeActionEnabledSafety, PTL DEF DeadlockFreedom
====
