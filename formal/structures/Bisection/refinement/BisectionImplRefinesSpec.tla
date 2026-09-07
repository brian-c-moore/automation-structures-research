---- MODULE BisectionImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for Bisection. Immutable domain_size, threshold, *)
(* and max_probes map to constants. probe maps to exactly one midpoint      *)
(* endpoint update. converged and observation methods stutter. The driver   *)
(* loop supplies progress; SchedulerFairnessRely states that temporal rely. *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals

CONSTANTS DomainSize, Threshold, MaxProbes
Pow2[k \in Nat] == IF k = 0 THEN 1 ELSE 2 * Pow2[k - 1]
ASSUME DomainSizeType == DomainSize \in Nat /\ DomainSize >= 2
ASSUME ThresholdType == Threshold \in 1..(DomainSize - 1)
ASSUME MaxProbesType == MaxProbes \in Nat
ASSUME DomainFits == DomainSize <= Pow2[MaxProbes]

VARIABLES domain_size, threshold, max_probes, lo, hi, probes_taken
vars == <<domain_size, threshold, max_probes, lo, hi, probes_taken>>

\* The Rust carrier uses lo + (hi - lo) / 2 to avoid u64 overflow. Under
\* lo <= hi its natural-number observation is the canonical midpoint below.
Mid == (lo + hi) \div 2
TypeInvariant ==
    /\ domain_size = DomainSize
    /\ threshold = Threshold
    /\ max_probes = MaxProbes
    /\ lo \in 0..domain_size
    /\ hi \in 0..domain_size
    /\ probes_taken \in Nat
Monotonicity == lo <= threshold /\ threshold <= hi
ProbeBound == probes_taken <= max_probes
WidthExpBound == hi - lo <= Pow2[max_probes - probes_taken]
ImplInvariant == TypeInvariant /\ Monotonicity /\ ProbeBound /\ WidthExpBound

Init ==
    /\ domain_size = DomainSize
    /\ threshold = Threshold
    /\ max_probes = MaxProbes
    /\ lo \in 0..threshold
    /\ hi \in threshold..domain_size
    /\ probes_taken = 0
    /\ ImplInvariant

ImplProbeLeft ==
    /\ ImplInvariant
    /\ hi - lo >= 2
    /\ Mid >= threshold
    /\ hi' = Mid
    /\ lo' = lo
    /\ probes_taken' = probes_taken + 1
    /\ UNCHANGED <<domain_size, threshold, max_probes>>
    /\ ImplInvariant'

ImplProbeRight ==
    /\ ImplInvariant
    /\ hi - lo >= 2
    /\ Mid < threshold
    /\ lo' = Mid + 1
    /\ hi' = hi
    /\ probes_taken' = probes_taken + 1
    /\ UNCHANGED <<domain_size, threshold, max_probes>>
    /\ ImplInvariant'

ImplReadOrConverged == UNCHANGED vars
ImplProgress == ImplProbeLeft \/ ImplProbeRight
ImplNext == ImplProgress \/ ImplReadOrConverged

B == INSTANCE Bisection WITH
        DomainSize <- DomainSize,
        Threshold <- Threshold,
        MaxProbes <- MaxProbes,
        lo <- lo,
        hi <- hi,
        probes_taken <- probes_taken

SchedulerFairnessRely ==
    WF_<<lo, hi, probes_taken>>(B!ProbeLeft \/ B!ProbeRight)
Spec == Init /\ [][ImplNext]_vars /\ SchedulerFairnessRely
SafetyRefinement == B!Init /\ [][B!Next]_(B!vars)
Refinement == B!Spec
====
