---- MODULE FiniteTopologyStreamGraph_Proof ----
\* Parametric safety proof for the general finite-topology streaming carrier.
\* The theorem covers arbitrary finite node, stream-edge, and state-edge sets
\* satisfying the declared topology assumptions. It does not prove fairness.
EXTENDS FiniteTopologyStreamGraph, Naturals, Sequences, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, TLAPS

Inv ==
    /\ TypeInvariant
    /\ CapacityBound
    /\ EdgeConservation
    /\ FanoutConservation
    /\ TerminalConsistency
    /\ SelectedInputExact

LEMMA EdgeCountPositive == EdgeCount \in Nat \ {0}
  <1>nat. EdgeCount \in Nat
    BY StreamEdgesFinite, FS_CardinalityType DEF EdgeCount
  <1>nz. EdgeCount # 0
    BY StreamEdgesFinite, StreamEdgesNonEmpty, FS_EmptySet DEF EdgeCount
  <1> QED  BY <1>nat, <1>nz

LEMMA NextCursorType ==
  ASSUME NEW e \in StreamEdges
  PROVE  NextCursor(e) \in 1..EdgeCount
  BY EdgeOrderType, EdgeCountPositive DEF NextCursor

LEMMA HeadTailReconstruct ==
  ASSUME NEW S, NEW q \in Seq(S), q # <<>>
  PROVE  q = <<Head(q)>> \o Tail(q)
  <1>lennat. Len(q) \in Nat  BY LenProperties
  <1>lennz. Len(q) # 0  BY EmptySeq
  <1>len. Len(q) \in Nat \ {0}  BY <1>lennat, <1>lennz
  <1>tail. Tail(q) = SubSeq(q, 2, Len(q))  BY TailIsSubSeq
  <1>whole. SubSeq(q, 1, Len(q)) = q
    <2>r. SubSeq(q, 1, Len(q)) = Restrict(q, 1..Len(q))
      BY <1>len, SubSeqRestrict
    <2>d. DOMAIN q = 1..Len(q)  BY LenProperties
    <2> QED  BY <2>r, <2>d
  <1>split. SubSeq(q, 1, Len(q)) =
        <<q[1]>> \o SubSeq(q, 2, Len(q))
    BY <1>len, SubSeqRecursive
  <1>head. Head(q) = q[1]  OBVIOUS
  <1> QED  BY <1>tail, <1>whole, <1>split, <1>head

LEMMA EdgeConservationFrame ==
  ASSUME EdgeConservation,
         queues' = queues, sent' = sent, received' = received,
         discarded' = discarded
  PROVE  EdgeConservation'
  <1> SUFFICES ASSUME NEW edge \in StreamEdges
               PROVE  sent'[edge] =
                  received'[edge] \o discarded'[edge] \o queues'[edge]
    BY DEF EdgeConservation
  <1>old. sent[edge] =
        received[edge] \o discarded[edge] \o queues[edge]
    BY DEF EdgeConservation
  <1> QED  BY <1>old

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY EdgeCountPositive, InitialNodesType DEF Init, TypeInvariant, EdgeStatuses
  <1>2. CapacityBound
    BY CapacityType DEF Init, CapacityBound
  <1>3. EdgeConservation
    BY ConcatEmptySeq DEF Init, EdgeConservation
  <1>4. FanoutConservation
    BY StreamEndpointsType DEF Init, FanoutConservation
  <1>5. TerminalConsistency
    BY DEF Init, TerminalConsistency, Drained, EdgeStatuses,
           OpenStatus, ClosingStatus, ClosedStatus, CancelledStatus,
           FailedStatus
  <1>6. SelectedInputExact  BY DEF Init, SelectedInputExact
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

LEMMA PublishInv ==
  ASSUME Inv, NEW n \in Nodes, NEW payload \in Payloads, Publish(n, payload)
  PROVE  Inv'
  <1>t. TypeInvariant  BY DEF Inv
  <1>b. CapacityBound  BY DEF Inv
  <1>c. EdgeConservation  BY DEF Inv
  <1>f. FanoutConservation  BY DEF Inv
  <1>x. TerminalConsistency  BY DEF Inv
  <1>s. SelectedInputExact  BY DEF Inv
  <1>1. TypeInvariant'
    BY <1>t, AppendProperties, EdgeCountPositive
       DEF Publish, TypeInvariant, PublishEnabled, Outgoing, EdgeStatuses
  <1>2. CapacityBound'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  Len(queues'[edge]) <= Capacity(edge)
      BY DEF CapacityBound
    <2>A. CASE edge \in Outgoing(n)
      <3>q. queues'[edge] = Append(queues[edge], payload)
        BY <2>A, SMT DEF Publish
      <3>room. Len(queues[edge]) < Capacity(edge)
        BY <2>A, SMT DEF Publish, PublishEnabled
      <3>len. Len(queues'[edge]) = Len(queues[edge]) + 1
        BY <1>t, <3>q, AppendProperties, SMT DEF TypeInvariant
      <3> QED  BY <3>room, <3>len, CapacityType, SMT
    <2>B. CASE edge \notin Outgoing(n)
      <3>1. queues'[edge] = queues[edge]
        BY <2>B, SMT DEF Publish
      <3> QED  BY <3>1, <1>b, SMT DEF CapacityBound
    <2> QED  BY <2>A, <2>B, SMT
  <1>3. EdgeConservation'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  sent'[edge] =
                    received'[edge] \o discarded'[edge] \o queues'[edge]
      BY DEF EdgeConservation
    <2>cases. edge \in Outgoing(n) \/ edge \notin Outgoing(n)
      OBVIOUS
    <2>A. CASE edge \in Outgoing(n)
      <3>src. StreamSource(edge) = n  BY <2>A, SMT DEF Outgoing
      <3>old. sent[edge] =
            received[edge] \o discarded[edge] \o queues[edge]
        BY <1>c DEF EdgeConservation
      <3>seqs. /\ sent[edge] \in Seq(Payloads)
                /\ received[edge] \in Seq(Payloads)
                /\ discarded[edge] \in Seq(Payloads)
                /\ queues[edge] \in Seq(Payloads)
        BY <1>t DEF TypeInvariant
      <3>single. <<payload>> \in Seq(Payloads)  OBVIOUS
      <3>step. Append(sent[edge], payload) =
            received[edge] \o discarded[edge]
                \o Append(queues[edge], payload)
        <4>sentseq. sent[edge] \in Seq(Payloads)  BY <3>seqs
        <4>qseq. queues[edge] \in Seq(Payloads)  BY <3>seqs
        <4>rd. received[edge] \o discarded[edge] \in Seq(Payloads)
          BY <3>seqs, ConcatProperties
        <4>a. Append(sent[edge], payload) = sent[edge] \o <<payload>>
          BY <4>sentseq, AppendIsConcat
        <4>q. Append(queues[edge], payload) =
              queues[edge] \o <<payload>>
          BY <4>qseq, AppendIsConcat
        <4>assoc.
            (received[edge] \o discarded[edge] \o queues[edge])
                \o <<payload>>
            = (received[edge] \o discarded[edge])
                \o (queues[edge] \o <<payload>>)
          BY <4>rd, <4>qseq, <3>single, ConcatAssociative
        <4> QED  BY <3>old, <4>a, <4>q, <4>assoc
      <3>change. /\ sent'[edge] = Append(sent[edge], payload)
                  /\ queues'[edge] = Append(queues[edge], payload)
                  /\ received'[edge] = received[edge]
                  /\ discarded'[edge] = discarded[edge]
        BY <2>A, SMT DEF Publish
      <3> QED  BY <3>step, <3>change, SMT
    <2>B. CASE edge \notin Outgoing(n)
      <3>old. sent[edge] =
            received[edge] \o discarded[edge] \o queues[edge]
        BY <1>c DEF EdgeConservation
      <3>change. /\ sent'[edge] = sent[edge]
                  /\ queues'[edge] = queues[edge]
                  /\ received'[edge] = received[edge]
                  /\ discarded'[edge] = discarded[edge]
        BY <2>B, SMT DEF Publish
      <3> QED  BY <3>old, <3>change
    <2> QED  BY <2>cases, <2>A, <2>B
  <1>4. FanoutConservation'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  sent'[edge] = published'[StreamSource(edge)]
      BY DEF FanoutConservation
    <2>A. CASE StreamSource(edge) = n
      <3>out. edge \in Outgoing(n)  BY <2>A, SMT DEF Outgoing
      <3>old. sent[edge] = published[n]
        BY <1>f, <2>A DEF FanoutConservation
      <3>change. /\ sent'[edge] = Append(sent[edge], payload)
                  /\ published'[n] = Append(published[n], payload)
        BY <3>out, <1>t, SMT DEF Publish, TypeInvariant
      <3> QED  BY <2>A, <3>old, <3>change, SMT
    <2>B. CASE StreamSource(edge) # n
      <3>out. edge \notin Outgoing(n)  BY <2>B, SMT DEF Outgoing
      <3>change. /\ sent'[edge] = sent[edge]
                  /\ published'[StreamSource(edge)] =
                        published[StreamSource(edge)]
        BY <3>out, <2>B, <1>t, StreamEndpointsType, SMT
           DEF Publish, TypeInvariant
      <3> QED  BY <1>f, <3>change, SMT DEF FanoutConservation
    <2> QED  BY <2>A, <2>B, SMT
  <1>5. TerminalConsistency'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  /\ edge_status'[edge]
                              \in {OpenStatus, ClosingStatus}
                              => discarded'[edge] = <<>>
                        /\ edge_status'[edge] = ClosedStatus =>
                            /\ Drained(edge)'
                            /\ discarded'[edge] = <<>>
                        /\ edge_status'[edge]
                              \in {CancelledStatus, FailedStatus}
                              => Drained(edge)'
      BY DEF TerminalConsistency
    <2>cases. edge \in Outgoing(n) \/ edge \notin Outgoing(n)
      OBVIOUS
    <2>A. CASE edge \in Outgoing(n)
      <3>open. edge_status[edge] = OpenStatus
        BY <2>A, SMT DEF Publish, PublishEnabled
      <3>discard. discarded[edge] = <<>>
        BY <1>x, <3>open, SMT DEF TerminalConsistency
      <3>change. /\ edge_status'[edge] = edge_status[edge]
                  /\ discarded'[edge] = discarded[edge]
        BY SMT DEF Publish
      <3> QED  BY <3>open, <3>discard, <3>change, SMT
                   DEF OpenStatus, ClosingStatus, ClosedStatus,
                       CancelledStatus, FailedStatus
    <2>B. CASE edge \notin Outgoing(n)
      BY <2>B, <1>x, SMT DEF Publish, TerminalConsistency, Drained
    <2> QED  BY <2>cases, <2>A, <2>B
  <1>6. SelectedInputExact'  BY <1>s DEF Publish, SelectedInputExact
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, SMT DEF Inv

LEMMA ReceiveSelectedInv ==
  ASSUME Inv, NEW n \in Nodes, NEW e \in StreamEdges, ReceiveSelected(n, e)
  PROVE  Inv'
  <1>t. TypeInvariant  BY DEF Inv
  <1>b. CapacityBound  BY DEF Inv
  <1>c. EdgeConservation  BY DEF Inv
  <1>f. FanoutConservation  BY DEF Inv
  <1>x. TerminalConsistency  BY DEF Inv
  <1>s. SelectedInputExact  BY DEF Inv
  <1>ready. /\ e \in Incoming(n) /\ Len(queues[e]) > 0
    BY SMT DEF ReceiveSelected, IsFirstReady, ReadyInputs
  <1>nonempty. queues[e] # <<>>
    BY <1>ready, <1>t, EmptySeq, SMT DEF TypeInvariant
  <1>headtype. Head(queues[e]) \in Payloads
    BY <1>t, <1>nonempty, HeadTailProperties DEF TypeInvariant
  <1>tailtype. Tail(queues[e]) \in Seq(Payloads)
    BY <1>t, <1>nonempty, HeadTailProperties DEF TypeInvariant
  <1>receivedtype. Append(received[e], Head(queues[e])) \in Seq(Payloads)
    BY <1>t, <1>headtype, AppendProperties DEF TypeInvariant
  <1>discard. discarded[e] = <<>>
    BY <1>t, <1>x, <1>nonempty, SMT
       DEF TypeInvariant, TerminalConsistency, Drained, EdgeStatuses,
           OpenStatus, ClosingStatus, ClosedStatus, CancelledStatus,
           FailedStatus
  <1>1. TypeInvariant'
    BY <1>t, <1>tailtype, <1>receivedtype, NextCursorType,
       EdgeCountPositive, SMT
       DEF ReceiveSelected, TypeInvariant
  <1>2. CapacityBound'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  Len(queues'[edge]) <= Capacity(edge)
      BY DEF CapacityBound
    <2>cases. edge = e \/ edge # e  OBVIOUS
    <2>A. CASE edge = e
      <3>len. Len(queues'[edge]) + 1 = Len(queues[edge])
        BY <2>A, <1>t, <1>nonempty, HeadTailProperties, SMT
           DEF ReceiveSelected, TypeInvariant
      <3>old. Len(queues[edge]) <= Capacity(edge)
        BY <1>b DEF CapacityBound
      <3> QED  BY <3>len, <3>old, CapacityType, SMT
    <2>B. CASE edge # e
      <3>1. queues'[edge] = queues[edge]
        BY <2>B, SMT DEF ReceiveSelected
      <3> QED  BY <3>1, <1>b, SMT DEF CapacityBound
    <2> QED  BY <2>cases, <2>A, <2>B
  <1>3. EdgeConservation'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  sent'[edge] =
                    received'[edge] \o discarded'[edge] \o queues'[edge]
      BY DEF EdgeConservation
    <2>cases. edge = e \/ edge # e  OBVIOUS
    <2>A. CASE edge = e
      <3>seqs. /\ sent[e] \in Seq(Payloads)
                /\ received[e] \in Seq(Payloads)
                /\ queues[e] \in Seq(Payloads)
        BY <1>t DEF TypeInvariant
      <3>conservation. sent[e] =
            (received[e] \o discarded[e]) \o queues[e]
        BY <1>c DEF EdgeConservation
      <3>prefix. received[e] \o discarded[e] = received[e]
        BY <3>seqs, <1>discard, ConcatEmptySeq
      <3>old. sent[e] = received[e] \o queues[e]
        BY <3>conservation, <3>prefix
      <3>head. Head(queues[e]) \in Payloads
        BY <3>seqs, <1>nonempty, HeadTailProperties
      <3>tail. Tail(queues[e]) \in Seq(Payloads)
        BY <3>seqs, <1>nonempty, HeadTailProperties
      <3>step. sent[e] =
            Append(received[e], Head(queues[e])) \o Tail(queues[e])
        <4>split. queues[e] = <<Head(queues[e])>> \o Tail(queues[e])
          BY <3>seqs, <1>nonempty, HeadTailReconstruct
        <4>append. Append(received[e], Head(queues[e])) =
              received[e] \o <<Head(queues[e])>>
          BY <3>seqs, <3>head, AppendIsConcat
        <4>single. <<Head(queues[e])>> \in Seq(Payloads)
          BY <3>head
        <4>assoc. received[e]
                \o (<<Head(queues[e])>> \o Tail(queues[e]))
            = (received[e] \o <<Head(queues[e])>>) \o Tail(queues[e])
          BY <3>seqs, <4>single, <3>tail, ConcatAssociative
        <4> QED  BY <3>old, <4>split, <4>append, <4>assoc
      <3>change. /\ sent'[edge] = sent[e]
                  /\ queues'[edge] = Tail(queues[e])
                  /\ received'[edge] =
                        Append(received[e], Head(queues[e]))
                  /\ discarded'[edge] = <<>>
        BY <2>A, <1>discard, <1>t, SMT
           DEF ReceiveSelected, TypeInvariant
      <3>receivedp. Append(received[e], Head(queues[e])) \in Seq(Payloads)
        BY <3>seqs, <3>head, AppendProperties
      <3> QED  BY <3>step, <3>change, <3>receivedp, ConcatEmptySeq
    <2>B. CASE edge # e
      <3>old. sent[edge] =
            received[edge] \o discarded[edge] \o queues[edge]
        BY <1>c DEF EdgeConservation
      <3>change. /\ sent'[edge] = sent[edge]
                  /\ queues'[edge] = queues[edge]
                  /\ received'[edge] = received[edge]
                  /\ discarded'[edge] = discarded[edge]
        BY <2>B, SMT DEF ReceiveSelected
      <3> QED  BY <3>old, <3>change
    <2> QED  BY <2>cases, <2>A, <2>B
  <1>4. FanoutConservation'
    BY <1>f, SMT DEF ReceiveSelected, FanoutConservation
  <1>5. TerminalConsistency'
    BY <1>t, <1>x, <1>nonempty, <1>discard, SMT
       DEF ReceiveSelected, TerminalConsistency, Drained, TypeInvariant,
           EdgeStatuses, OpenStatus, ClosingStatus, ClosedStatus,
           CancelledStatus, FailedStatus
  <1>6. SelectedInputExact'
    BY <1>s, SMT DEF ReceiveSelected, SelectedInputExact
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, SMT DEF Inv

LEMMA ReceiveSynchronizedInv ==
  ASSUME Inv, NEW n \in Nodes, ReceiveSynchronized(n)
  PROVE  Inv'
  <1>t. TypeInvariant  BY DEF Inv
  <1>b. CapacityBound  BY DEF Inv
  <1>c. EdgeConservation  BY DEF Inv
  <1>f. FanoutConservation  BY DEF Inv
  <1>x. TerminalConsistency  BY DEF Inv
  <1>s. SelectedInputExact  BY DEF Inv
  <1>nonempty. \A edge \in Incoming(n) : queues[edge] # <<>>
    BY <1>t, EmptySeq, SMT
       DEF ReceiveSynchronized, SynchronizedReady, Incoming, TypeInvariant
  <1>heads. \A edge \in Incoming(n) : Head(queues[edge]) \in Payloads
    BY <1>t, <1>nonempty, HeadTailProperties DEF Incoming, TypeInvariant
  <1>tails. \A edge \in Incoming(n) : Tail(queues[edge]) \in Seq(Payloads)
    BY <1>t, <1>nonempty, HeadTailProperties DEF Incoming, TypeInvariant
  <1>receivedtypes. \A edge \in Incoming(n) :
      Append(received[edge], Head(queues[edge])) \in Seq(Payloads)
    BY <1>t, <1>heads, AppendProperties DEF Incoming, TypeInvariant
  <1>1. TypeInvariant'
    BY <1>t, <1>tails, <1>receivedtypes, SMT
       DEF ReceiveSynchronized, Incoming, TypeInvariant
  <1>2. CapacityBound'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  Len(queues'[edge]) <= Capacity(edge)
      BY DEF CapacityBound
    <2>cases. edge \in Incoming(n) \/ edge \notin Incoming(n)
      OBVIOUS
    <2>A. CASE edge \in Incoming(n)
      <3>ne. queues[edge] # <<>>
        BY <2>A, <1>nonempty
      <3>len. Len(queues'[edge]) + 1 = Len(queues[edge])
        BY <2>A, <1>t, <3>ne, HeadTailProperties, SMT
           DEF ReceiveSynchronized, TypeInvariant
      <3>old. Len(queues[edge]) <= Capacity(edge)
        BY <1>b DEF CapacityBound
      <3> QED  BY <3>len, <3>old, CapacityType, SMT
    <2>B. CASE edge \notin Incoming(n)
      <3>1. queues'[edge] = queues[edge]
        BY <2>B, SMT DEF ReceiveSynchronized
      <3> QED  BY <3>1, <1>b, SMT DEF CapacityBound
    <2> QED  BY <2>cases, <2>A, <2>B
  <1>3. EdgeConservation'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  sent'[edge] =
                    received'[edge] \o discarded'[edge] \o queues'[edge]
      BY DEF EdgeConservation
    <2>cases. edge \in Incoming(n) \/ edge \notin Incoming(n)
      OBVIOUS
    <2>A. CASE edge \in Incoming(n)
      <3>ne. queues[edge] # <<>>
        BY <2>A, <1>nonempty
      <3>discard. discarded[edge] = <<>>
        BY <1>t, <1>x, <3>ne, SMT
           DEF TypeInvariant, TerminalConsistency, Drained, EdgeStatuses,
               OpenStatus, ClosingStatus, ClosedStatus, CancelledStatus,
               FailedStatus
      <3>seqs. /\ sent[edge] \in Seq(Payloads)
                /\ received[edge] \in Seq(Payloads)
                /\ queues[edge] \in Seq(Payloads)
        BY <1>t DEF TypeInvariant
      <3>conservation. sent[edge] =
            (received[edge] \o discarded[edge]) \o queues[edge]
        BY <1>c DEF EdgeConservation
      <3>prefix. received[edge] \o discarded[edge] = received[edge]
        BY <3>seqs, <3>discard, ConcatEmptySeq
      <3>old. sent[edge] = received[edge] \o queues[edge]
        BY <3>conservation, <3>prefix
      <3>head. Head(queues[edge]) \in Payloads
        BY <3>seqs, <3>ne, HeadTailProperties
      <3>tail. Tail(queues[edge]) \in Seq(Payloads)
        BY <3>seqs, <3>ne, HeadTailProperties
      <3>step. sent[edge] =
            Append(received[edge], Head(queues[edge]))
                \o Tail(queues[edge])
        <4>split. queues[edge] =
              <<Head(queues[edge])>> \o Tail(queues[edge])
          BY <3>seqs, <3>ne, HeadTailReconstruct
        <4>append. Append(received[edge], Head(queues[edge])) =
              received[edge] \o <<Head(queues[edge])>>
          BY <3>seqs, <3>head, AppendIsConcat
        <4>single. <<Head(queues[edge])>> \in Seq(Payloads)
          BY <3>head
        <4>assoc. received[edge]
                \o (<<Head(queues[edge])>> \o Tail(queues[edge]))
            = (received[edge] \o <<Head(queues[edge])>>)
                \o Tail(queues[edge])
          BY <3>seqs, <4>single, <3>tail, ConcatAssociative
        <4> QED  BY <3>old, <4>split, <4>append, <4>assoc
      <3>change. /\ sent'[edge] = sent[edge]
                  /\ queues'[edge] = Tail(queues[edge])
                  /\ received'[edge] =
                        Append(received[edge], Head(queues[edge]))
                  /\ discarded'[edge] = <<>>
        BY <2>A, <3>discard, <1>t, SMT
           DEF ReceiveSynchronized, TypeInvariant
      <3>receivedp. Append(received[edge], Head(queues[edge]))
            \in Seq(Payloads)
        BY <3>seqs, <3>head, AppendProperties
      <3> QED  BY <3>step, <3>change, <3>receivedp, ConcatEmptySeq
    <2>B. CASE edge \notin Incoming(n)
      <3>old. sent[edge] =
            received[edge] \o discarded[edge] \o queues[edge]
        BY <1>c DEF EdgeConservation
      <3>change. /\ sent'[edge] = sent[edge]
                  /\ queues'[edge] = queues[edge]
                  /\ received'[edge] = received[edge]
                  /\ discarded'[edge] = discarded[edge]
        BY <2>B, SMT DEF ReceiveSynchronized
      <3> QED  BY <3>old, <3>change
    <2> QED  BY <2>cases, <2>A, <2>B
  <1>4. FanoutConservation'
    BY <1>f, SMT DEF ReceiveSynchronized, FanoutConservation
  <1>5. TerminalConsistency'
    BY <1>t, <1>x, <1>nonempty, SMT
       DEF ReceiveSynchronized, Incoming, TerminalConsistency, Drained,
           TypeInvariant, EdgeStatuses,
           OpenStatus, ClosingStatus, ClosedStatus, CancelledStatus,
           FailedStatus
  <1>6. SelectedInputExact'
    BY <1>s, SMT DEF ReceiveSynchronized, SelectedInputExact
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, SMT DEF Inv

LEMMA RequestCloseInv ==
  ASSUME Inv, NEW e \in StreamEdges, RequestClose(e)
  PROVE  Inv'
  <1>t. TypeInvariant  BY DEF Inv
  <1>b. CapacityBound  BY DEF Inv
  <1>c. EdgeConservation  BY DEF Inv
  <1>f. FanoutConservation  BY DEF Inv
  <1>x. TerminalConsistency  BY DEF Inv
  <1>s. SelectedInputExact  BY DEF Inv
  <1>open. edge_status[e] = OpenStatus  BY DEF RequestClose
  <1>discard. discarded[e] = <<>>
    BY <1>x, <1>open DEF TerminalConsistency
  <1>unch. /\ queues' = queues
             /\ sent' = sent
             /\ received' = received
             /\ discarded' = discarded
             /\ published' = published
             /\ cursor' = cursor
             /\ reached' = reached
             /\ selection_valid' = selection_valid
    BY SMT DEF RequestClose
  <1>1. TypeInvariant'
    BY <1>t, <1>unch, SMT
       DEF RequestClose, TypeInvariant, EdgeStatuses,
           OpenStatus, ClosingStatus, ClosedStatus
  <1>2. CapacityBound'  BY <1>b, <1>unch, SMT DEF CapacityBound
  <1>3. EdgeConservation'
    BY <1>c, <1>unch, EdgeConservationFrame
  <1>4. FanoutConservation'
    BY <1>f, <1>unch, SMT DEF FanoutConservation
  <1>5. TerminalConsistency'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  /\ edge_status'[edge]
                              \in {OpenStatus, ClosingStatus}
                              => discarded'[edge] = <<>>
                        /\ edge_status'[edge] = ClosedStatus =>
                            /\ Drained(edge)'
                            /\ discarded'[edge] = <<>>
                        /\ edge_status'[edge]
                              \in {CancelledStatus, FailedStatus}
                              => Drained(edge)'
      BY DEF TerminalConsistency
    <2>A. CASE edge = e
      BY <2>A, <1>open, <1>discard, <1>unch, SMT
         DEF RequestClose, Drained, OpenStatus, ClosingStatus,
             ClosedStatus, CancelledStatus, FailedStatus
    <2>B. CASE edge # e
      BY <2>B, <1>x, <1>unch, SMT
         DEF RequestClose, TerminalConsistency, Drained
    <2> QED  BY <2>A, <2>B
  <1>6. SelectedInputExact'
    BY <1>s, <1>unch, SMT DEF SelectedInputExact
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

LEMMA FinalizeCloseInv ==
  ASSUME Inv, NEW e \in StreamEdges, FinalizeClose(e)
  PROVE  Inv'
  <1>t. TypeInvariant  BY DEF Inv
  <1>b. CapacityBound  BY DEF Inv
  <1>c. EdgeConservation  BY DEF Inv
  <1>f. FanoutConservation  BY DEF Inv
  <1>x. TerminalConsistency  BY DEF Inv
  <1>s. SelectedInputExact  BY DEF Inv
  <1>closing. edge_status[e] = ClosingStatus  BY DEF FinalizeClose
  <1>drained. Drained(e)  BY DEF FinalizeClose
  <1>discard. discarded[e] = <<>>
    BY <1>x, <1>closing DEF TerminalConsistency
  <1>unch. /\ queues' = queues
             /\ sent' = sent
             /\ received' = received
             /\ discarded' = discarded
             /\ published' = published
             /\ cursor' = cursor
             /\ reached' = reached
             /\ selection_valid' = selection_valid
    BY SMT DEF FinalizeClose
  <1>1. TypeInvariant'
    BY <1>t, <1>unch, SMT
       DEF FinalizeClose, TypeInvariant, EdgeStatuses, ClosedStatus
  <1>2. CapacityBound'  BY <1>b, <1>unch, SMT DEF CapacityBound
  <1>3. EdgeConservation'
    BY <1>c, <1>unch, EdgeConservationFrame
  <1>4. FanoutConservation'
    BY <1>f, <1>unch, SMT DEF FanoutConservation
  <1>5. TerminalConsistency'
    BY <1>x, <1>closing, <1>drained, <1>discard, <1>unch, SMT
       DEF FinalizeClose, TerminalConsistency, Drained, OpenStatus,
           ClosingStatus, ClosedStatus, CancelledStatus, FailedStatus
  <1>6. SelectedInputExact'
    BY <1>s, <1>unch, SMT DEF SelectedInputExact
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

LEMMA TerminateInv ==
  ASSUME Inv, NEW e \in StreamEdges,
         NEW outcome \in {CancelledStatus, FailedStatus},
         Terminate(e, outcome)
  PROVE  Inv'
  <1>t. TypeInvariant  BY DEF Inv
  <1>b. CapacityBound  BY DEF Inv
  <1>c. EdgeConservation  BY DEF Inv
  <1>f. FanoutConservation  BY DEF Inv
  <1>x. TerminalConsistency  BY DEF Inv
  <1>s. SelectedInputExact  BY DEF Inv
  <1>live. edge_status[e] \in {OpenStatus, ClosingStatus}
    BY DEF Terminate
  <1>discard. discarded[e] = <<>>
    BY <1>x, <1>live DEF TerminalConsistency
  <1>1. TypeInvariant'
    BY <1>t, <1>discard, ConcatProperties, SMT
       DEF Terminate, TypeInvariant, EdgeStatuses
  <1>2. CapacityBound'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  Len(queues'[edge]) <= Capacity(edge)
      BY DEF CapacityBound
    <2>A. CASE edge = e
      <3>empty. queues'[edge] = <<>>
        BY <2>A, <1>t, SMT DEF Terminate, TypeInvariant
      <3>cap. Capacity(edge) \in Nat \ {0}  BY CapacityType
      <3> QED  BY <3>empty, <3>cap, EmptySeq
    <2>B. CASE edge # e
      BY <2>B, <1>b, SMT DEF Terminate, CapacityBound
    <2> QED  BY <2>A, <2>B
  <1>3. EdgeConservation'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  sent'[edge] =
                    received'[edge] \o discarded'[edge] \o queues'[edge]
      BY DEF EdgeConservation
    <2>A. CASE edge = e
      <3>seqs. /\ sent[e] \in Seq(Payloads)
                /\ received[e] \in Seq(Payloads)
                /\ queues[e] \in Seq(Payloads)
        BY <1>t DEF TypeInvariant
      <3>conservation. sent[e] =
            (received[e] \o discarded[e]) \o queues[e]
        BY <1>c DEF EdgeConservation
      <3>prefix. received[e] \o discarded[e] = received[e]
        BY <3>seqs, <1>discard, ConcatEmptySeq
      <3>old. sent[e] = received[e] \o queues[e]
        BY <3>conservation, <3>prefix
      <3>change. /\ sent'[edge] = sent[e]
                  /\ received'[edge] = received[e]
                  /\ discarded'[edge] = queues[e]
                  /\ queues'[edge] = <<>>
        BY <2>A, <1>discard, <1>t, SMT DEF Terminate, TypeInvariant
      <3>rq. received[e] \o queues[e] \in Seq(Payloads)
        BY <3>seqs, ConcatProperties
      <3> QED  BY <3>old, <3>change, <3>rq, ConcatEmptySeq
    <2>B. CASE edge # e
      <3>old. sent[edge] =
            received[edge] \o discarded[edge] \o queues[edge]
        BY <1>c DEF EdgeConservation
      <3>change. /\ sent'[edge] = sent[edge]
                  /\ received'[edge] = received[edge]
                  /\ discarded'[edge] = discarded[edge]
                  /\ queues'[edge] = queues[edge]
        BY <2>B, SMT DEF Terminate
      <3> QED  BY <3>old, <3>change
    <2> QED  BY <2>A, <2>B
  <1>4. FanoutConservation'
    BY <1>f, SMT DEF Terminate, FanoutConservation
  <1>5. TerminalConsistency'
    <2> SUFFICES ASSUME NEW edge \in StreamEdges
                 PROVE  /\ edge_status'[edge]
                              \in {OpenStatus, ClosingStatus}
                              => discarded'[edge] = <<>>
                        /\ edge_status'[edge] = ClosedStatus =>
                            /\ Drained(edge)'
                            /\ discarded'[edge] = <<>>
                        /\ edge_status'[edge]
                              \in {CancelledStatus, FailedStatus}
                              => Drained(edge)'
      BY DEF TerminalConsistency
    <2>A. CASE edge = e
      BY <2>A, <1>live, <1>discard, <1>t, SMT
         DEF Terminate, Drained, TypeInvariant, OpenStatus,
             ClosingStatus, ClosedStatus, CancelledStatus, FailedStatus
    <2>B. CASE edge # e
      BY <2>B, <1>x, <1>t, SMT
         DEF Terminate, TerminalConsistency, Drained, TypeInvariant
    <2> QED  BY <2>A, <2>B
  <1>6. SelectedInputExact'
    BY <1>s, SMT DEF Terminate, SelectedInputExact
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

LEMMA CancelInv ==
  ASSUME Inv, NEW e \in StreamEdges, Cancel(e)
  PROVE  Inv'
  BY TerminateInv DEF Cancel

LEMMA FailInv ==
  ASSUME Inv, NEW e \in StreamEdges, Fail(e)
  PROVE  Inv'
  BY TerminateInv DEF Fail

LEMMA AdvanceStateInv ==
  ASSUME Inv, NEW e \in StateEdges, AdvanceState(e)
  PROVE  Inv'
  <1>t. TypeInvariant  BY DEF Inv
  <1>b. CapacityBound  BY DEF Inv
  <1>c. EdgeConservation  BY DEF Inv
  <1>f. FanoutConservation  BY DEF Inv
  <1>x. TerminalConsistency  BY DEF Inv
  <1>s. SelectedInputExact  BY DEF Inv
  <1>unch. /\ queues' = queues
             /\ sent' = sent
             /\ received' = received
             /\ discarded' = discarded
             /\ published' = published
             /\ edge_status' = edge_status
             /\ cursor' = cursor
             /\ selection_valid' = selection_valid
    BY SMT DEF AdvanceState, StreamProjection
  <1>reach. reached' \subseteq Nodes
    BY <1>t, StateEndpointsType, SMT DEF AdvanceState, TypeInvariant
  <1>1. TypeInvariant'
    BY <1>t, <1>unch, <1>reach DEF TypeInvariant
  <1>2. CapacityBound'  BY <1>b, <1>unch, SMT DEF CapacityBound
  <1>3. EdgeConservation'
    BY <1>c, <1>unch, EdgeConservationFrame
  <1>4. FanoutConservation'
    BY <1>f, <1>unch, SMT DEF FanoutConservation
  <1>5. TerminalConsistency'
    BY <1>x, <1>unch, SMT DEF TerminalConsistency, Drained
  <1>6. SelectedInputExact'
    BY <1>s, <1>unch, SMT DEF SelectedInputExact
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1>0. CASE UNCHANGED vars
    <2>u. /\ queues' = queues
              /\ sent' = sent
              /\ received' = received
              /\ discarded' = discarded
              /\ published' = published
              /\ edge_status' = edge_status
              /\ cursor' = cursor
              /\ reached' = reached
              /\ selection_valid' = selection_valid
      BY <1>0, SMT DEF vars
    <2> QED  BY <2>u DEF Inv, TypeInvariant, CapacityBound,
                            EdgeConservation, FanoutConservation,
                            TerminalConsistency, SelectedInputExact, Drained
  <1>S. CASE StreamStep
    BY <1>S, PublishInv, ReceiveSelectedInv, ReceiveSynchronizedInv,
       RequestCloseInv, FinalizeCloseInv, CancelInv, FailInv DEF StreamStep
  <1>T. CASE StateStep
    BY <1>T, AdvanceStateInv DEF StateStep
  <1>N. CASE Next  BY <1>N, <1>S, <1>T DEF Next
  <1> QED  BY <1>0, <1>N

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                  BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant  BY Safety, PTL DEF Inv
THEOREM CapacitySafety == Spec => []CapacityBound  BY Safety, PTL DEF Inv
THEOREM ConservationSafety == Spec => []EdgeConservation
  BY Safety, PTL DEF Inv
THEOREM FanoutSafety == Spec => []FanoutConservation
  BY Safety, PTL DEF Inv
THEOREM TerminalSafety == Spec => []TerminalConsistency
  BY Safety, PTL DEF Inv
THEOREM SelectedInputSafety == Spec => []SelectedInputExact
  BY Safety, PTL DEF Inv

THEOREM SelectedReceiveExactEffect ==
  \A n \in Nodes, e \in StreamEdges :
    TypeInvariant /\ ReceiveSelected(n, e) =>
      /\ IsFirstReady(n, e)
      /\ queues'[e] = Tail(queues[e])
      /\ received'[e] = Append(received[e], Head(queues[e]))
      /\ \A other \in StreamEdges \ {e} :
          /\ queues'[other] = queues[other]
          /\ received'[other] = received[other]
  <1> SUFFICES ASSUME NEW n \in Nodes, NEW e \in StreamEdges,
                       TypeInvariant, ReceiveSelected(n, e)
               PROVE  /\ IsFirstReady(n, e)
                       /\ queues'[e] = Tail(queues[e])
                       /\ received'[e] =
                            Append(received[e], Head(queues[e]))
                       /\ \A other \in StreamEdges \ {e} :
                            /\ queues'[other] = queues[other]
                            /\ received'[other] = received[other]
    OBVIOUS
  <1>self. /\ IsFirstReady(n, e)
            /\ queues'[e] = Tail(queues[e])
            /\ received'[e] = Append(received[e], Head(queues[e]))
    BY SMT DEF ReceiveSelected, TypeInvariant
  <1>other. \A other \in StreamEdges \ {e} :
        /\ queues'[other] = queues[other]
        /\ received'[other] = received[other]
    BY SMT DEF ReceiveSelected, TypeInvariant
  <1> QED  BY <1>self, <1>other

THEOREM SynchronizedReceiveExactEffect ==
  ASSUME TypeInvariant, NEW n \in Nodes, ReceiveSynchronized(n)
  PROVE  /\ \A e \in Incoming(n) :
               /\ queues'[e] = Tail(queues[e])
               /\ received'[e] = Append(received[e], Head(queues[e]))
          /\ \A other \in StreamEdges \ Incoming(n) :
               /\ queues'[other] = queues[other]
               /\ received'[other] = received[other]
  <1>inside. \A e \in Incoming(n) :
        /\ queues'[e] = Tail(queues[e])
        /\ received'[e] = Append(received[e], Head(queues[e]))
    <2> SUFFICES ASSUME NEW e \in Incoming(n)
                 PROVE  /\ queues'[e] = Tail(queues[e])
                         /\ received'[e] =
                              Append(received[e], Head(queues[e]))
      OBVIOUS
    <2>edge. e \in StreamEdges  BY DEF Incoming
    <2> QED  BY <2>edge, SMT DEF ReceiveSynchronized, TypeInvariant
  <1>outside. \A other \in StreamEdges \ Incoming(n) :
        /\ queues'[other] = queues[other]
        /\ received'[other] = received[other]
    <2> SUFFICES ASSUME NEW other \in StreamEdges \ Incoming(n)
                 PROVE  /\ queues'[other] = queues[other]
                         /\ received'[other] = received[other]
      OBVIOUS
    <2> QED  BY SMT DEF ReceiveSynchronized, TypeInvariant
  <1> QED  BY <1>inside, <1>outside

THEOREM StreamStepFramesState == StreamStep => UNCHANGED StateProjection
  <1> SUFFICES ASSUME StreamStep PROVE UNCHANGED StateProjection  OBVIOUS
  <1>P. CASE \E n \in Nodes, payload \in Payloads : Publish(n, payload)
    BY <1>P DEF Publish, StateProjection
  <1>R. CASE \E n \in Nodes, e \in StreamEdges : ReceiveSelected(n, e)
    BY <1>R DEF ReceiveSelected, StateProjection
  <1>S. CASE \E n \in Nodes : ReceiveSynchronized(n)
    BY <1>S DEF ReceiveSynchronized, StateProjection
  <1>C. CASE \E e \in StreamEdges : RequestClose(e)
    BY <1>C DEF RequestClose, StateProjection
  <1>F. CASE \E e \in StreamEdges : FinalizeClose(e)
    BY <1>F DEF FinalizeClose, StateProjection
  <1>X. CASE \E e \in StreamEdges : Cancel(e)
    BY <1>X DEF Cancel, Terminate, StateProjection
  <1>E. CASE \E e \in StreamEdges : Fail(e)
    BY <1>E DEF Fail, Terminate, StateProjection
  <1> QED  BY <1>P, <1>R, <1>S, <1>C, <1>F, <1>X, <1>E DEF StreamStep

THEOREM StateStepFramesStream == StateStep => UNCHANGED StreamProjection
  BY DEF StateStep, AdvanceState

THEOREM RejectedPublishStutters ==
  \A n \in Nodes, payload \in Payloads :
      RejectedPublish(n, payload) => UNCHANGED vars
  BY DEF RejectedPublish

THEOREM RejectedSelectedReceiveStutters ==
  \A n \in Nodes : RejectedSelectedReceive(n) => UNCHANGED vars
  BY DEF RejectedSelectedReceive
====
