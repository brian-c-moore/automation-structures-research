---- MODULE PiCalculus ----
\* ====================================================================
\* Tier 1 framework encoding (bounded study configuration).
\* PiCalculus -> StreamGraph / Message / Dynamic_Addressable / Per_Rendezvous.
\* Evidence: trace_equivalence. See configurations/tier1/pi_calculus.toml
\* for citations.
\*
\* Per Fowler, Lindley & Wadler (2017) "Mixing Metaphors: Actors as
\* Channels and Channels as Actors", a pi-calculus term with
\* name-passing translates bidirectionally to an actor calculus. The
\* reproduction places pi-calculus at the same configuration as
\* actors (StreamGraph + Message + Dynamic_Addressable) with the
\* name-passing dependency policy.
\* ====================================================================
EXTENDS Naturals

Modality   == "StreamGraph"
Invocation == "Message"
Topology   == "Dynamic_Addressable"
Lifecycle  == "Per_Rendezvous"

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
