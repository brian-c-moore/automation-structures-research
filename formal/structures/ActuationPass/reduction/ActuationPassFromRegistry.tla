---- MODULE ActuationPassFromRegistry ----
\* Tested reduction of ActuationPass over two ResourceRegistry instances and
\* admitted glue.
\*
\*   allocation <- registry 1 through a defaulted-NULL projection;
\*   effects    <- registry 2 through the same projection; and
\*   complete   <- a marker.
\*
\* Allocate and Deallocate are registry writes. Actuate atomically reads the
\* allocation registry and writes the effects registry. `ActuationScope` and
\* `EffectFidelity` therefore route through component state and actions.
\* `PassCompleteness` instead depends on the marker's state-sensitive Finish
\* guard; the paired negative control splits that guard from the commit.
\*
\* The result is conditional on the fused component steps being atomic. The
\* defaulted views are derived projections, not held state.

EXTENDS FiniteSets

CONSTANTS Seats, Resources, NULL

\* Two ResourceRegistry component states + the Marker glue.
VARIABLES e_alloc, e_eff, complete

vars == <<e_alloc, e_eff, complete>>

RegA == INSTANCE ResourceRegistry WITH Keys <- Seats, Values <- Resources,
                                       entries <- e_alloc
RegE == INSTANCE ResourceRegistry WITH Keys <- Seats, Values <- Resources,
                                       entries <- e_eff

\* The kept primitive's own obligation, carried unchanged (faithful use),
\* once per instance.
AllocUnique == RegA!UniqueMapping
EffUnique == RegE!UniqueMapping

\* CF-001 Projections: the defaulted-NULL views (the EquivalenceClass
\* pattern). UniqueMapping is what makes the CHOOSE deterministic. Factored
\* through one parameterized reader so the two instances share a single
\* read-back argument.
ReadIn(E, s) ==
    IF \E r \in Resources : <<s, r>> \in E
    THEN CHOOSE r \in Resources : <<s, r>> \in E
    ELSE NULL

ReadA(s) == ReadIn(e_alloc, s)
ReadE(s) == ReadIn(e_eff, s)

AllocView == [s \in Seats |-> ReadA(s)]
EffView == [s \in Seats |-> ReadE(s)]

\* The TARGET's completeness obligation (O3), restated over the
\* construction's own state so the glue-admissibility gate can identify which
\* stratum carries it. Declaring only component invariants would make a target
\* obligation carried by declared glue invisible to that gate. O1 and O2 need
\* no such restatement -- they constrain only the two registries, which are
\* component-bound and not declared glue, so they cannot change the verdict.
\* Written out rather than instanced (APL!PassCompleteness) because the gate
\* is textual and must see the variable name.
MappedPassCompleteness ==
    complete => \A s \in Seats : ReadA(s) /= NULL => ReadE(s) /= NULL

TypeInvariant ==
    /\ RegA!TypeInvariant
    /\ RegE!TypeInvariant
    /\ complete \in BOOLEAN

\* The target's allocation is any partial seat->resource map at Init; the
\* effect registry starts empty; the pass starts open.
Init ==
    /\ \E D \in SUBSET Seats, f \in [Seats -> Resources] :
           e_alloc = {<<s, f[s]>> : s \in D}
    /\ e_eff = {}
    /\ complete = FALSE

\* THE PASS: read registry #1, register into registry #2, one step.
CActuate(s) ==
    /\ ~complete
    /\ ReadE(s) = NULL
    /\ ReadA(s) /= NULL
    /\ e_eff' = {x \in e_eff : x[1] /= s} \cup {<<s, ReadA(s)>>}   \* Register
    /\ UNCHANGED <<e_alloc, complete>>

\* THE ENVIRONMENT: Register / Deregister on registry #1, verbatim.
CAllocate(s, r) ==
    /\ ~complete
    /\ ReadA(s) = NULL
    /\ e_alloc' = {x \in e_alloc : x[1] /= s} \cup {<<s, r>>}      \* Register
    /\ UNCHANGED <<e_eff, complete>>

CDeallocate(s) ==
    /\ ~complete
    /\ ReadA(s) /= NULL
    /\ ReadE(s) = NULL
    /\ e_alloc' = {x \in e_alloc : x[1] /= s}                      \* Deregister
    /\ UNCHANGED <<e_eff, complete>>

\* CLOSURE: the coverage check and the marker, one step.
CFinish ==
    /\ ~complete
    /\ \A s \in Seats : ReadA(s) /= NULL => ReadE(s) /= NULL
    /\ complete' = TRUE
    /\ UNCHANGED <<e_alloc, e_eff>>

Next ==
    \/ \E s \in Seats : CActuate(s)
    \/ \E s \in Seats, r \in Resources : CAllocate(s, r)
    \/ \E s \in Seats : CDeallocate(s)
    \/ CFinish

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to ActuationPass ---
\* Two of the target's three variables are pure derivations; the third is
\* the declared Marker.
APL == INSTANCE ActuationPass WITH
        allocation <- AllocView,
        effects    <- EffView,
        complete   <- complete,
        Seats      <- Seats,
        Resources  <- Resources,
        NULL       <- NULL

\* If this holds, every behaviour of the composition is an ActuationPass
\* behaviour.
ActuationPassRefinement == APL!Spec
====
