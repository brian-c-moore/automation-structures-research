---- MODULE RateLimit_Proof ----
(* TLAPS proof of RateLimit safety.

   MaxPerWindowType, WindowDurationType and MaxClockType are RateLimit's own
   constant assumptions and arrive by EXTENDS. They belong to the
   specification, not to this proof: stated only here they would bound what is
   proved while leaving the module itself satisfiable at constants that
   falsify its invariants. *)
EXTENDS RateLimit, Naturals, TLAPS

Inv == TypeInvariant /\ WindowCountBound /\ WindowStartNotFuture

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY MaxPerWindowType DEF Init, TypeInvariant
  <1>2. WindowCountBound
    BY MaxPerWindowType DEF Init, WindowCountBound
  <1>3. WindowStartNotFuture
    BY DEF Init, WindowStartNotFuture
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, WindowCountBound, WindowStartNotFuture
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE TryAcquire
    <2>a. count \in 0..MaxPerWindow            OBVIOUS
    <2>b. window_start \in Nat                  OBVIOUS
    <2>c. clock \in Nat                         OBVIOUS
    <2>d. window_start <= clock                 OBVIOUS
    \* TryAcquire's action body is an IF-THEN-ELSE-IF-ELSE chain. Expand it
    \* manually as a disjunction of mutually-exclusive guarded conjunctions.
    <2>e. \/ (clock - window_start >= WindowDuration
              /\ window_start' = clock
              /\ count' = 1
              /\ clock' = clock)
          \/ (~(clock - window_start >= WindowDuration)
              /\ count < MaxPerWindow
              /\ count' = count + 1
              /\ window_start' = window_start
              /\ clock' = clock)
          \/ (~(clock - window_start >= WindowDuration)
              /\ ~(count < MaxPerWindow)
              /\ window_start' = window_start
              /\ count' = count
              /\ clock' = clock)
      BY <1>1 DEF TryAcquire, vars
    <2>1. CASE clock - window_start >= WindowDuration
              /\ window_start' = clock
              /\ count' = 1
              /\ clock' = clock
      <3>1. count' \in 0..MaxPerWindow
        BY <2>1, MaxPerWindowType
      <3> QED  BY <2>1, <3>1, MaxPerWindowType
    <2>2. CASE ~(clock - window_start >= WindowDuration)
              /\ count < MaxPerWindow
              /\ count' = count + 1
              /\ window_start' = window_start
              /\ clock' = clock
      <3>1. count' \in 0..MaxPerWindow
        BY <2>2, <2>a, MaxPerWindowType
      <3> QED  BY <2>2, <3>1, <2>b, <2>c, <2>d, MaxPerWindowType
    <2>3. CASE ~(clock - window_start >= WindowDuration)
              /\ ~(count < MaxPerWindow)
              /\ window_start' = window_start
              /\ count' = count
              /\ clock' = clock
      BY <2>3, <2>a, <2>b, <2>c, <2>d, MaxPerWindowType
    <2> QED  BY <2>e, <2>1, <2>2, <2>3
  <1>2. CASE Tick
    <2>1. clock' = clock + 1                    BY <1>2 DEF Tick
    <2>2. UNCHANGED <<count, window_start>>     BY <1>2 DEF Tick
    <2>3. count' \in 0..MaxPerWindow            BY <2>2
    <2>4. window_start' \in Nat                 BY <2>2
    <2>5. clock' \in Nat                        BY <2>1
    <2>6. window_start' <= clock'               BY <2>1, <2>2
    <2>7. count' <= MaxPerWindow                BY <2>2, <2>3
    <2> QED  BY <2>3, <2>4, <2>5, <2>6, <2>7
  <1>3. CASE Next
    BY <1>3, <1>1, <1>2 DEF Next
  <1> QED  BY <1>0, <1>3

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant       BY Safety, PTL DEF Inv
THEOREM WindowCountBoundSafety == Spec => []WindowCountBound  BY Safety, PTL DEF Inv
THEOREM WindowStartNotFutureSafety == Spec => []WindowStartNotFuture  BY Safety, PTL DEF Inv
====
