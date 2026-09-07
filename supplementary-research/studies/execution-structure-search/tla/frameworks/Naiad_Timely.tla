---- MODULE Naiad_Timely ----
\* Tier 1 framework encoding (bounded study configuration).
\* Naiad_Timely -> StreamGraph / Continuous_Progress / Declared_With_Iteration / Pointstamp_Based.
\* Evidence: documented_behavior. See configurations/tier1/naiad_timely.toml for citations.
EXTENDS Naturals

Modality   == "StreamGraph"
Invocation == "Continuous_Progress"
Topology   == "Declared_With_Iteration"
Lifecycle  == "Pointstamp_Based"

\* Bounded state to keep the model checker finite.
VARIABLE step
Init == step = 0
Next == (step = 0 /\ step' = 1) \/ (step = 1 /\ UNCHANGED step)
Spec == Init /\ [][Next]_<<step>>

ModalityValid == Modality \in {"Sequential","ForkJoin","StepGraph","StepGraph_Cyclic","StreamGraph"}
AxisConsistency ==
    /\ (Modality = "Sequential"  => Topology = "None")
    /\ (Modality = "ForkJoin"    => Topology \in {"None","None_Ranked"})
    /\ (Modality \in {"StepGraph","StepGraph_Cyclic"} => Topology \notin {"None","None_Ranked"})
    /\ (Modality = "StreamGraph" => Topology \notin {"None","None_Ranked"})

OK == ModalityValid /\ AxisConsistency
====
