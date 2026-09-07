---- MODULE SignalImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated delivery atomicity fault: notify two pending listeners in one  *)
(* commit. Disjointness and provenance remain true, but one canonical      *)
(* NotifyListener action moves exactly one listener.                        *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS SignalImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultNotifyTwo ==
    /\ AdjacentInvariant
    /\ {0, 1} \subseteq pending_notifications
    /\ pending_notifications' = pending_notifications \ {0, 1}
    /\ notified' = notified \cup {0, 1}
    /\ UNCHANGED <<num_values, num_listeners,
                    current_value, change_observed>>
    /\ AdjacentInvariant'

FaultNext == ImplSetValue(1) \/ FaultNotifyTwo \/ ImplReadOrReject
FaultRefinement == S!Spec
====
