---- MODULE ActuationPassFromRegistry_NEG ----
\* Negative control for ActuationPassFromRegistry: one deliberately
\* broken step, proving the refinement check is non-vacuous.
\*
\* Fault injection: CFinish's coverage check is split from the marker write. The
\* check now records its verdict in a staging flag (`checked`), and a second
\* step promotes that flag to `complete`. Nothing else changes -- the two
\* registries, the pass step, and the environment are verbatim.
\*
\* This control decomposes PassCompleteness. Finish's guard quantifies over
\* the GUARDED STATE (the live registries), not over its arguments, so the
\* fusion is load-bearing and this split must break the refinement. A clean
\* run would instead mean O3's check/act fusion carries nothing, that O3 is
\* an emergent non-obligation of the NoSelfLoops kind, and that the Marker is
\* admissible glue.
\*
\* REQUIRED OUTCOME: VIOLATED. Between the check
\* and the promotion, CAllocate can register a seat that never gets actuated,
\* and the promoted `complete` then reports closure over an unapplied seat --
\* a state the target's fused Finish cannot reach.

EXTENDS FiniteSets

CONSTANTS Seats, Resources, NULL

VARIABLES e_alloc, e_eff, complete, checked

vars == <<e_alloc, e_eff, complete, checked>>

RegA == INSTANCE ResourceRegistry WITH Keys <- Seats, Values <- Resources,
                                       entries <- e_alloc
RegE == INSTANCE ResourceRegistry WITH Keys <- Seats, Values <- Resources,
                                       entries <- e_eff

AllocUnique == RegA!UniqueMapping
EffUnique == RegE!UniqueMapping

ReadIn(E, s) ==
    IF \E r \in Resources : <<s, r>> \in E
    THEN CHOOSE r \in Resources : <<s, r>> \in E
    ELSE NULL

ReadA(s) == ReadIn(e_alloc, s)
ReadE(s) == ReadIn(e_eff, s)

AllocView == [s \in Seats |-> ReadA(s)]
EffView == [s \in Seats |-> ReadE(s)]

TypeInvariant ==
    /\ RegA!TypeInvariant
    /\ RegE!TypeInvariant
    /\ complete \in BOOLEAN
    /\ checked \in BOOLEAN

Init ==
    /\ \E D \in SUBSET Seats, f \in [Seats -> Resources] :
           e_alloc = {<<s, f[s]>> : s \in D}
    /\ e_eff = {}
    /\ complete = FALSE
    /\ checked = FALSE

CActuate(s) ==
    /\ ~complete
    /\ ReadE(s) = NULL
    /\ ReadA(s) /= NULL
    /\ e_eff' = {x \in e_eff : x[1] /= s} \cup {<<s, ReadA(s)>>}
    /\ UNCHANGED <<e_alloc, complete, checked>>

CAllocate(s, r) ==
    /\ ~complete
    /\ ReadA(s) = NULL
    /\ e_alloc' = {x \in e_alloc : x[1] /= s} \cup {<<s, r>>}
    /\ UNCHANGED <<e_eff, complete, checked>>

CDeallocate(s) ==
    /\ ~complete
    /\ ReadA(s) /= NULL
    /\ ReadE(s) = NULL
    /\ e_alloc' = {x \in e_alloc : x[1] /= s}
    /\ UNCHANGED <<e_eff, complete, checked>>

\* First fault transition: perform the coverage check and stage the verdict.
CCheck ==
    /\ ~complete
    /\ ~checked
    /\ \A s \in Seats : ReadA(s) /= NULL => ReadE(s) /= NULL
    /\ checked' = TRUE
    /\ UNCHANGED <<e_alloc, e_eff, complete>>

\* Second fault transition: promote the staged verdict to closure.
CPromote ==
    /\ ~complete
    /\ checked
    /\ complete' = TRUE
    /\ UNCHANGED <<e_alloc, e_eff, checked>>

Next ==
    \/ \E s \in Seats : CActuate(s)
    \/ \E s \in Seats, r \in Resources : CAllocate(s, r)
    \/ \E s \in Seats : CDeallocate(s)
    \/ CCheck
    \/ CPromote

Spec == Init /\ [][Next]_vars

APL == INSTANCE ActuationPass WITH
        allocation <- AllocView,
        effects    <- EffView,
        complete   <- complete,
        Seats      <- Seats,
        Resources  <- Resources,
        NULL       <- NULL

ActuationPassRefinement == APL!Spec
====
