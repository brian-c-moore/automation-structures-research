---- MODULE Bazel ----
\* Tier 1 framework axis assignment, checked for internal consistency:
\* Bazel -> StepGraph / Demand_Pull / Declared_DAG_ContentHash / Incremental.
\* This module encodes no Bazel behavior -- step is a two-state device and
\* OK mentions no variable; BazelBehavior.tla is the behavioral spec.
\* Evidence: direct_comparison. See configurations/tier1/bazel.toml for citations.
EXTENDS Naturals

Modality   == "StepGraph"
Invocation == "Demand_Pull"
Topology   == "Declared_DAG_ContentHash"
Lifecycle  == "Incremental"

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
