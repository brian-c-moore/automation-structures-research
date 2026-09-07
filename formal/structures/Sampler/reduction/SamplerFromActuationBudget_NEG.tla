---- MODULE SamplerFromActuationBudget_NEG ----
\* Negative control for SamplerFromActuationBudget: proof that the
\* refinement check has teeth on the obligation the verdict turns on.
\*
\* EXACTLY ONE change from the positive construction: CZero no longer uses
\* the component's own `Act!Deallocate`. It writes the withdrawal by hand,
\* with the component's ownership guard `effects[i] = NULL` dropped and
\* everything else -- the typing, the ledger, the draw, the mapping --
\* verbatim. So the mutation is precisely "stop using the primitive as a
\* primitive at one step".
\*
\* The collateral breakage is expected. This same mutation also breaks the
\* component's OWN obligations (ActuationScope and EffectFidelity), because
\* the target's SupportConsistency and the component's ActuationScope are the
\* same statement under the mapping. One mutation breaks both properties in
\* lockstep, which is what the positive construction claims. The three
\* component invariants
\* the positive carries (ActScope, ActFidelity, ActCompleteness) are
\* therefore not declared here, so the trace isolates the ACTION PROPERTY --
\* the first two because the mutation breaks them by design, and
\* ActCompleteness, inert either way, because it is vacuous in both modules
\* (complete is FALSE throughout; neither Next contains Finish).
\* TypeInvariant and BudgetSafety are declared and
\* still hold, showing the mutation is localized to the withdrawal.

EXTENDS Naturals, FiniteSets

CONSTANTS Items, SampleSize, MaxProb

VARIABLES a_alloc, a_eff, a_complete,
          b_capacity, b_allocated, b_reserved, b_pending

vars == <<a_alloc, a_eff, a_complete,
          b_capacity, b_allocated, b_reserved, b_pending>>

Act == INSTANCE ActuationPass WITH Seats      <- Items,
                                       Resources  <- 1..MaxProb,
                                       NULL       <- 0,
                                       allocation <- a_alloc,
                                       effects    <- a_eff,
                                       complete   <- a_complete
Bgt == INSTANCE Budget WITH Capacity <- SampleSize,
                            capacity <- b_capacity,
                            allocated <- b_allocated,
                            reserved <- b_reserved,
                            pending_eviction <- b_pending

BudgetSafety == Bgt!SafetyInvariant

Selected == Act!Actuated

TypeInvariant ==
    /\ Act!TypeInvariant
    /\ b_capacity = SampleSize
    /\ b_allocated \in 0..SampleSize
    /\ b_reserved = 0
    /\ b_pending = 0
    /\ Cardinality(Selected) = b_allocated

Init ==
    /\ Act!Init
    /\ Bgt!Init

CDraw(i) ==
    /\ Act!Actuate(i)
    /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
    /\ b_allocated' = b_allocated + 1
    /\ UNCHANGED <<b_capacity, b_reserved, b_pending>>

\* MUTATED: the component's Deallocate written out by hand, without its
\* ownership guard `a_eff[i] = 0`.
CZero(i) ==
    /\ ~a_complete
    /\ a_alloc[i] /= 0
    /\ a_alloc' = [a_alloc EXCEPT ![i] = 0]
    /\ UNCHANGED <<a_eff, a_complete>>
    /\ UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending>>

Next ==
    \/ \E i \in Items : CDraw(i)
    \/ \E i \in Items : CZero(i)

Spec == Init /\ [][Next]_vars

SMP == INSTANCE Sampler WITH
        distribution <- a_alloc,
        selected     <- Selected,
        Items        <- Items,
        SampleSize   <- SampleSize,
        MaxProb      <- MaxProb

\* MUST VIOLATE.
SamplerRefinement == SMP!Spec
====
