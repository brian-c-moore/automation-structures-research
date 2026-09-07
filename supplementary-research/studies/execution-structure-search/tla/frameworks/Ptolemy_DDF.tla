---- MODULE Ptolemy_DDF ----
\* Tier 1 framework encoding (bounded study configuration).
\* Ptolemy_DDF -> StreamGraph / Dynamic_Schedule / Declared_Dynamic / Per_Firing.
\* Evidence: documented_behavior. See configurations/tier1/ptolemy_ddf.toml for citations.
EXTENDS Naturals

Modality   == "StreamGraph"
Invocation == "Dynamic_Schedule"
Topology   == "Declared_Dynamic"
Lifecycle  == "Per_Firing"

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
