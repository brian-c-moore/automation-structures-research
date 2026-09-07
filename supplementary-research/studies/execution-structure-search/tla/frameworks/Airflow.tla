---- MODULE Airflow ----
\* Tier 1 framework axis assignment, checked for internal consistency:
\* Airflow -> StepGraph / Time_Or_DepCompletion / Declared_DAG_Task / Rerun_From_Failure.
\* This module encodes no Airflow behavior -- step is a two-state device and
\* OK mentions no variable; AirflowBehavior.tla is the behavioral spec.
\* Evidence: direct_comparison. See configurations/tier1/airflow.toml for citations.
EXTENDS Naturals

Modality   == "StepGraph"
Invocation == "Time_Or_DepCompletion"
Topology   == "Declared_DAG_Task"
Lifecycle  == "Rerun_From_Failure"

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
