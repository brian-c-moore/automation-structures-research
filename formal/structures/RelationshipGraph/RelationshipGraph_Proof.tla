---- MODULE RelationshipGraph_Proof ----
(* TLAPS proof that both graph views remain well typed and agree after every
   add/remove step, and that the selected loop policy is preserved. *)
EXTENDS RelationshipGraph, Naturals, FiniteSets, TLAPS

Inv == TypeInvariant /\ AdjacencyConsistency /\ SelectedLoopPolicy

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant       BY DEF Init, TypeInvariant
  <1>2. AdjacencyConsistency
    <2> SUFFICES ASSUME NEW src \in Nodes
                 PROVE adjacency[src] = {dst \in Nodes : \E w \in 0..MaxWeight : <<src, dst, w>> \in edges}
      BY DEF AdjacencyConsistency
    <2>1. adjacency[src] = {}  BY DEF Init
    <2>2. {dst \in Nodes : \E w \in 0..MaxWeight : <<src, dst, w>> \in edges} = {}
      BY DEF Init
    <2> QED  BY <2>1, <2>2
  <1>3. SelectedLoopPolicy
    <2>1. NoSelfLoops
      <3> SUFFICES ASSUME NEW n \in Nodes PROVE n \notin adjacency[n]
        BY DEF NoSelfLoops
      <3>1. adjacency[n] = {}  BY DEF Init
      <3> QED  BY <3>1
    <2> QED  BY <2>1 DEF SelectedLoopPolicy
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, AdjacencyConsistency, SelectedLoopPolicy
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars, Inv, SelectedLoopPolicy, NoSelfLoops
  <1>A. CASE \E s, d \in Nodes, w \in 0..MaxWeight : AddEdge(s, d, w)
    <2> SUFFICES ASSUME NEW src \in Nodes, NEW dst \in Nodes, NEW w \in 0..MaxWeight,
                         AddEdge(src, dst, w)
                 PROVE Inv'
      BY <1>A
    <2>a. AllowSelfLoops \/ src /= dst                         BY DEF AddEdge
    <2>b. edges' = edges \cup {<<src, dst, w>>}               BY DEF AddEdge
    <2>c. adjacency' = [adjacency EXCEPT ![src] = @ \cup {dst}]
      BY DEF AddEdge
    <2>1. TypeInvariant'
      <3>1. edges' \subseteq (Nodes \X Nodes \X (0..MaxWeight))
        BY <2>b
      <3>2. adjacency' \in [Nodes -> SUBSET Nodes]
        BY <2>c
      <3> QED  BY <3>1, <3>2
    <2>2. AdjacencyConsistency'
      <3> SUFFICES ASSUME NEW src2 \in Nodes
                   PROVE adjacency'[src2] = {dst2 \in Nodes : \E ww \in 0..MaxWeight : <<src2, dst2, ww>> \in edges'}
        BY DEF AdjacencyConsistency
      <3>A. CASE src2 = src
        <4>1. adjacency'[src2] = adjacency[src] \cup {dst}
          BY <2>c, <3>A
        <4>2. adjacency[src] = {d2 \in Nodes : \E ww \in 0..MaxWeight : <<src, d2, ww>> \in edges}
          OBVIOUS
        <4>3. {dst2 \in Nodes : \E ww \in 0..MaxWeight : <<src2, dst2, ww>> \in edges'}
              = (adjacency[src] \cup {dst})
          BY <2>b, <3>A, <4>2
        <4> QED  BY <4>1, <4>3
      <3>B. CASE src2 /= src
        <4>1. adjacency'[src2] = adjacency[src2]
          BY <2>c, <3>B
        <4>2. adjacency[src2] = {d2 \in Nodes : \E ww \in 0..MaxWeight : <<src2, d2, ww>> \in edges}
          OBVIOUS
        <4>3. {dst2 \in Nodes : \E ww \in 0..MaxWeight : <<src2, dst2, ww>> \in edges'}
              = adjacency[src2]
          BY <2>b, <3>B, <4>2
        <4> QED  BY <4>1, <4>3
      <3> QED  BY <3>A, <3>B
    <2>3. SelectedLoopPolicy'
      <3>A. CASE AllowSelfLoops
        BY <3>A DEF SelectedLoopPolicy
      <3>B. CASE ~AllowSelfLoops
        <4>a. src /= dst  BY <2>a, <3>B
        <4>b. NoSelfLoops  BY <3>B DEF SelectedLoopPolicy
        <4>1. NoSelfLoops'
          <5> SUFFICES ASSUME NEW n \in Nodes PROVE n \notin adjacency'[n]
            BY DEF NoSelfLoops
          <5>A. CASE n = src
            <6>1. adjacency'[n] = adjacency[src] \cup {dst}  BY <2>c, <5>A
            <6>2. src \notin adjacency[src]  BY <4>b DEF NoSelfLoops
            <6> QED  BY <6>1, <6>2, <4>a, <5>A
          <5>B. CASE n /= src
            <6>1. adjacency'[n] = adjacency[n]  BY <2>c, <5>B
            <6>2. n \notin adjacency[n]  BY <4>b DEF NoSelfLoops
            <6> QED  BY <6>1, <6>2
          <5> QED  BY <5>A, <5>B
        <4> QED  BY <4>1 DEF SelectedLoopPolicy
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2, <2>3
  <1>B. CASE \E s, d \in Nodes : RemoveEdge(s, d)
    <2> SUFFICES ASSUME NEW src \in Nodes, NEW dst \in Nodes,
                         RemoveEdge(src, dst)
                 PROVE Inv'
      BY <1>B
    <2>b. edges' = {e \in edges : ~(e[1] = src /\ e[2] = dst)}
      BY DEF RemoveEdge
    <2>c. adjacency' = [adjacency EXCEPT ![src] = @ \ {dst}]
      BY DEF RemoveEdge
    <2>1. TypeInvariant'
      <3>1. edges' \subseteq (Nodes \X Nodes \X (0..MaxWeight))
        BY <2>b
      <3>2. adjacency' \in [Nodes -> SUBSET Nodes]
        BY <2>c
      <3> QED  BY <3>1, <3>2
    <2>2. AdjacencyConsistency'
      <3> SUFFICES ASSUME NEW src2 \in Nodes
                   PROVE adjacency'[src2] = {dst2 \in Nodes : \E ww \in 0..MaxWeight : <<src2, dst2, ww>> \in edges'}
        BY DEF AdjacencyConsistency
      <3>A. CASE src2 = src
        <4>1. adjacency'[src2] = adjacency[src] \ {dst}
          BY <2>c, <3>A
        <4>2. adjacency[src] = {d2 \in Nodes : \E ww \in 0..MaxWeight : <<src, d2, ww>> \in edges}
          OBVIOUS
        <4>3. {dst2 \in Nodes : \E ww \in 0..MaxWeight : <<src2, dst2, ww>> \in edges'}
              = adjacency[src] \ {dst}
          BY <2>b, <3>A, <4>2
        <4> QED  BY <4>1, <4>3
      <3>B. CASE src2 /= src
        <4>1. adjacency'[src2] = adjacency[src2]
          BY <2>c, <3>B
        <4>2. adjacency[src2] = {d2 \in Nodes : \E ww \in 0..MaxWeight : <<src2, d2, ww>> \in edges}
          OBVIOUS
        <4>3. {dst2 \in Nodes : \E ww \in 0..MaxWeight : <<src2, dst2, ww>> \in edges'}
              = adjacency[src2]
          BY <2>b, <3>B, <4>2
        <4> QED  BY <4>1, <4>3
      <3> QED  BY <3>A, <3>B
    <2>3. SelectedLoopPolicy'
      <3>A. CASE AllowSelfLoops
        BY <3>A DEF SelectedLoopPolicy
      <3>B. CASE ~AllowSelfLoops
        <4>a. NoSelfLoops  BY <3>B DEF SelectedLoopPolicy
        <4>1. NoSelfLoops'
          <5> SUFFICES ASSUME NEW n \in Nodes PROVE n \notin adjacency'[n]
            BY DEF NoSelfLoops
          <5>A. CASE n = src
            <6>1. adjacency'[n] = adjacency[src] \ {dst}  BY <2>c, <5>A
            <6>2. src \notin adjacency[src]  BY <4>a DEF NoSelfLoops
            <6> QED  BY <6>1, <6>2, <5>A
          <5>B. CASE n /= src
            <6>1. adjacency'[n] = adjacency[n]  BY <2>c, <5>B
            <6>2. n \notin adjacency[n]  BY <4>a DEF NoSelfLoops
            <6> QED  BY <6>1, <6>2
          <5> QED  BY <5>A, <5>B
        <4> QED  BY <4>1 DEF SelectedLoopPolicy
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2, <2>3
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant         BY Safety, PTL DEF Inv
THEOREM AdjacencyConsistencySafety == Spec => []AdjacencyConsistency  BY Safety, PTL DEF Inv
THEOREM SelectedLoopPolicySafety == Spec => []SelectedLoopPolicy  BY Safety, PTL DEF Inv
THEOREM NoSelfLoopsSafety == ~AllowSelfLoops => (Spec => []NoSelfLoops)
  <1> SUFFICES ASSUME ~AllowSelfLoops, Spec PROVE []NoSelfLoops  OBVIOUS
  <1>1. []SelectedLoopPolicy  BY Safety, PTL DEF Inv
  <1> QED  BY <1>1, PTL DEF SelectedLoopPolicy
====
