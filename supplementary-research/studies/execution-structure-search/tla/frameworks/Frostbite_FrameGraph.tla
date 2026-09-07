---- MODULE Frostbite_FrameGraph ----
\* Tier 1 framework encoding (bounded study configuration).
\* Frostbite_FrameGraph -> StreamGraph / Vsync / Rebuilt_Per_Frame / Per_Frame.
\* Evidence: documented_behavior. See configurations/tier1/frostbite_framegraph.toml for citations.
EXTENDS Naturals

Modality   == "StreamGraph"
Invocation == "Vsync"
Topology   == "Rebuilt_Per_Frame"
Lifecycle  == "Per_Frame"

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
