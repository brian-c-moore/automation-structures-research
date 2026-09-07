---- MODULE SamplerFromActuationBudget ----
\* Tested reduction of Sampler over ActuationPass and Budget.
\*
\*   distribution <- ActuationPass.allocation with 0 as the out-of-support
\*                   sentinel;
\*   selected     <- ActuationPass.Actuated; and
\*   sample bound <- Budget, coupled by Cardinality(Selected) = allocated.
\*
\* Actuate supplies Sampler's fused support-read and selection commit;
\* Deallocate supplies the guarded environment withdrawal. Budget supplies the
\* sample-size ceiling. Every held variable belongs to a component; `Selected`
\* is the component's own derived projection.
\*
\* Qualification: this construction uses a strict sub-behavior of ActuationPass.
\* It never takes Allocate or Finish, so PassCompleteness is vacuous here. The
\* reduction result is conditional on the fused component steps being atomic.

EXTENDS Naturals, FiniteSets

CONSTANTS Items, SampleSize, MaxProb

\* No glue variables: a_* are ActuationPass's own state, b_* are
\* Budget's.
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

\* The kept primitives' OWN obligations, carried unchanged as checked
\* invariants (the faithful-use standard): the construction
\* provably maintains a legal ActuationPass and a legal Budget at every
\* step.
ActScope == Act!ActuationScope
ActFidelity == Act!EffectFidelity
ActCompleteness == Act!PassCompleteness
BudgetSafety == Bgt!SafetyInvariant

\* CF-001 Projection -- and it is the COMPONENT's own projection, read out
\* rather than held.
Selected == Act!Actuated

TypeInvariant ==
    /\ Act!TypeInvariant
    /\ b_capacity = SampleSize
    /\ b_allocated \in 0..SampleSize
    /\ b_reserved = 0
    /\ b_pending = 0
    \* The coupling that makes the ledger the sample count.
    /\ Cardinality(Selected) = b_allocated

Init ==
    /\ Act!Init
    /\ Bgt!Init

\* The draw: the component's own fused read-and-mark, plus Budget's
\* affordability test and ledger advance (TryAllocate(1)), in one step.
CDraw(i) ==
    /\ Act!Actuate(i)
    /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
    /\ b_allocated' = b_allocated + 1
    /\ UNCHANGED <<b_capacity, b_reserved, b_pending>>

\* The environment writer: the component's own
\* withdrawal, verbatim, ownership guard included.
CZero(i) ==
    /\ Act!Deallocate(i)
    /\ UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending>>

Next ==
    \/ \E i \in Items : CDraw(i)
    \/ \E i \in Items : CZero(i)

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to Sampler ---
SMP == INSTANCE Sampler WITH
        distribution <- a_alloc,
        selected     <- Selected,
        Items        <- Items,
        SampleSize   <- SampleSize,
        MaxProb      <- MaxProb

SamplerRefinement == SMP!Spec
====
