---- MODULE Signal_Proof ----
(* TLAPS proof of Signal typing, delivery-set disjointness, and notification
   provenance through the guarded change epoch. *)
EXTENDS Signal, FiniteSets, TLAPS

Inv == TypeInvariant /\ PendingNotifiedDisjointness /\ NotificationProvenance

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant               BY DEF Init, TypeInvariant
  <1>2. PendingNotifiedDisjointness
    BY DEF Init, PendingNotifiedDisjointness
  <1>3. NotificationProvenance
    BY DEF Init, NotificationProvenance
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, PendingNotifiedDisjointness,
              NotificationProvenance
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Next
    <2>A. CASE \E v \in Values : SetValue(v)
      <3> SUFFICES ASSUME NEW v \in Values, SetValue(v) PROVE Inv'
        BY <2>A
      <3>1. current_value' \in Values        BY DEF SetValue
      <3>2. change_observed' \in BOOLEAN      BY DEF SetValue
      <3>3. pending_notifications' = Listeners  BY DEF SetValue
      <3>4. notified' = {}                    BY DEF SetValue
      <3>5. change_observed'                  BY DEF SetValue
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>B. CASE \E l \in Listeners : NotifyListener(l)
      <3> SUFFICES ASSUME NEW l \in Listeners, NotifyListener(l) PROVE Inv'
        BY <2>B
      <3>a. pending_notifications' = pending_notifications \ {l}
        BY DEF NotifyListener
      <3>b. notified' = notified \cup {l}     BY DEF NotifyListener
      <3>c. current_value' = current_value    BY DEF NotifyListener
      <3>d. l \in pending_notifications       BY DEF NotifyListener
      <3>e. change_observed' = change_observed  BY DEF NotifyListener
      <3>1. current_value' \in Values         BY <3>c
      <3>2. change_observed' \in BOOLEAN      BY <3>e
      <3>3. pending_notifications' \subseteq Listeners  BY <3>a
      <3>4. notified' \subseteq Listeners     BY <3>b
      <3>5. pending_notifications' \cap notified' = {}
        \* pending'\notified' = (pending\{l}) \cap (notified \cup {l})
        \*   = ((pending\{l}) \cap notified) \cup ((pending\{l}) \cap {l})
        \*   = subset of (pending \cap notified) which is {} by IH, union {}.
        BY <3>a, <3>b
      <3>6. NotificationProvenance'
        BY <3>a, <3>b, <3>d, <3>e DEF NotificationProvenance
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <2> QED  BY <2>A, <2>B, <1>1 DEF Next
  <1> QED  BY <1>0, <1>1

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant                      BY Safety, PTL DEF Inv
THEOREM PendingNotifiedDisjointnessSafety ==
    Spec => []PendingNotifiedDisjointness
  BY Safety, PTL DEF Inv

THEOREM NotificationProvenanceSafety == Spec => []NotificationProvenance
  BY Safety, PTL DEF Inv
====
