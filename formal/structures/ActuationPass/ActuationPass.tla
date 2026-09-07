---- MODULE ActuationPass ----
(* Apply side effects to the resources currently assigned to a set of seats.

   `allocation` is environment-written state. `Actuate` reads an allocation
   and records the corresponding effect in one transition; splitting that
   read from the commit permits a deallocation race. A seat with a recorded
   effect stays inside the pass's ownership boundary, so the environment may
   not withdraw it before closure.

   The primary contract clauses are:

     EffectFidelity   -- the recorded effect is the allocated resource; and
     PassCompleteness -- closure is reported only after every allocated seat
                         has a recorded effect.

   `Actuated` is derived from `effects`; it is not duplicated state.
   ActuationScope follows from EffectFidelity in the proof; it is not an
   independent contract clause.
   This carrier makes no exactly-once claim.                                *)
EXTENDS FiniteSets

CONSTANTS Seats, Resources, NULL

VARIABLES allocation,   \* the live allocation record; the environment writes it
          effects,      \* effects[s] = the resource the operation was applied
                        \* to for seat s, or NULL if not yet applied
          complete      \* the pass has reported closure

vars == <<allocation, effects, complete>>

\* The applied set is read out of the effect record, not
\* held beside it.
Actuated == {s \in Seats : effects[s] /= NULL}

TypeInvariant ==
    /\ allocation \in [Seats -> Resources \cup {NULL}]
    /\ effects    \in [Seats -> Resources \cup {NULL}]
    /\ complete   \in BOOLEAN

\* Only allocated seats are actuated.
ActuationScope ==
    \A s \in Actuated : allocation[s] /= NULL

\* The operation was applied
\* to the resource the seat's allocation held at application time.
EffectFidelity ==
    \A s \in Seats : effects[s] /= NULL => effects[s] = allocation[s]

\* Completeness of application: the pass does
\* not report closure while an allocated seat remains unapplied.
PassCompleteness ==
    complete => \A s \in Seats : allocation[s] /= NULL => effects[s] /= NULL

Init ==
    /\ allocation \in [Seats -> Resources \cup {NULL}]
    /\ effects = [s \in Seats |-> NULL]
    /\ complete = FALSE

\* THE PASS. Read the seat's allocation and apply the operation to it in one
\* step. Splitting this is exactly
\* ActuationPassDecomposed.
Actuate(s) ==
    /\ ~complete
    /\ effects[s] = NULL
    /\ allocation[s] /= NULL
    /\ effects' = [effects EXCEPT ![s] = allocation[s]]
    /\ UNCHANGED <<allocation, complete>>

\* The environment's allocation writer.
Allocate(s, r) ==
    /\ ~complete
    /\ allocation[s] = NULL
    /\ allocation' = [allocation EXCEPT ![s] = r]
    /\ UNCHANGED <<effects, complete>>

\* Withdrawal. Guarded by the pass's ownership of what it has already acted
\* on: a side effect is irrevocable, so a seat whose operation has been
\* applied is inside the snapshot boundary until the pass closes.
Deallocate(s) ==
    /\ ~complete
    /\ allocation[s] /= NULL
    /\ effects[s] = NULL
    /\ allocation' = [allocation EXCEPT ![s] = NULL]
    /\ UNCHANGED <<effects, complete>>

\* CLOSURE. Check that nothing eligible remains and record the closure in the
\* same step. Splitting these admits a new allocation between the check and
\* the flag, which is what PassCompleteness polices.
Finish ==
    /\ ~complete
    /\ \A s \in Seats : allocation[s] /= NULL => effects[s] /= NULL
    /\ complete' = TRUE
    /\ UNCHANGED <<allocation, effects>>

Next ==
    \/ \E s \in Seats : Actuate(s)
    \/ \E s \in Seats, r \in Resources : Allocate(s, r)
    \/ \E s \in Seats : Deallocate(s)
    \/ Finish

Spec == Init /\ [][Next]_vars

\* Spec => []TypeInvariant, []EffectFidelity, []PassCompleteness are proved in
\* ActuationPass_Proof.tla; []ActuationScope is proved there as a
\* corollary of EffectFidelity.
====
