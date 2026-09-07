---- MODULE GitHub_Actions ----
\* Tier 1 framework encoding (bounded study configuration).
\* GitHub_Actions -> StepGraph / VCS_Event / Declared_DAG / Rerun_Job.
\* Evidence: documented_behavior. See configurations/tier1/github_actions.toml for citations.
EXTENDS Naturals

Modality   == "StepGraph"
Invocation == "VCS_Event"
Topology   == "Declared_DAG"
Lifecycle  == "Rerun_Job"

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
