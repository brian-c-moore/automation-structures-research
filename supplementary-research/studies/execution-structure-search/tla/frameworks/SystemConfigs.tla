---- MODULE SystemConfigs ----
\* ====================================================================
\* PER-SYSTEM ENCODING (docs/execution-modalities.md)
\*
\* Each named system's documented semantics is encoded as a configuration
\* vector (modality, invocation, topology, dependencies, lifecycle), and the
\* configuration's behavior under the specs is checked against the system's
\* documented behavior on a small set of representative scenarios.
\*
\* This module encodes 29 systems from the cross-domain table as
\* configuration vectors and checks the well-formedness of each.
\* Behavioral scenarios for representative systems (Make, Bazel, Erlang,
\* Flink-pipelined, Airflow, Naiad/Timely, pi-calculus) live in the
\* per-system *Behavior.tla modules in this directory.
\* ====================================================================
EXTENDS Naturals, FiniteSets

ModalityTags ==
    {"Sequential", "ForkJoin", "StepGraph", "StepGraph_Cyclic",
     "StreamGraph"}

InvocationTags ==
    {"Manual", "Time", "Programmatic", "Demand_Pull",
     "Time_Or_DepCompletion", "Event_Or_Programmatic", "VCS_Event",
     "VCS_Or_Webhook", "Security_Event", "HTTP_Or_Schedule",
     "Continuous", "Continuous_Differential", "Continuous_Progress",
     "Continuous_Clock_Or_Sample", "UI_Or_Data_Event", "Vsync",
     "Message", "Message_Or_Continuous",
     "PerToken_Or_PerMessage"}

TopologyTags ==
    {"None", "None_Ranked", "Declared_DAG_File",
     "Declared_DAG_ContentHash", "Declared_DAG_Task", "Declared_DAG",
     "Declared_Playbook", "Declared_Visual_Flow", "Workflow_As_Code",
     "Declared_Anonymous", "Declared_Topology", "Declared_Incremental",
     "Declared_With_Iteration", "Declared_Element_Graph",
     "Declared_Filter_Chain", "Declared_Observable_Chain",
     "Rebuilt_Per_Frame", "Dynamic_Addressable", "Virtual_Addressable",
     "Mixed_Declared_And_Dynamic", "Declared_Often_Cyclic",
     "Declared"}

LifecycleTags ==
    {"None", "Rerun", "Sync_Barrier", "Reexecute_Failed",
     "Rerun_Changed", "Incremental", "Rerun_From_Failure", "Rerun_Job",
     "Rerun_Pipeline", "Per_Incident", "Per_Execution",
     "Continuation_As_New", "Checkpoint_Restart",
     "Per_Topology_Recovery", "Maintained_Views", "Pointstamp_Based",
     "Per_Pipeline", "Per_Invocation", "Subscription", "Per_Frame",
     "Supervision_Tree", "Supervision", "Persistence_Backed",
     "Atomic_Stream"}

\* ----- Systems from the cross-domain table -----

SystemNames ==
    {"Bash_script", "cron_job", "GNU_parallel", "MPI_scatter_gather",
     "MapReduce", "Make", "Bazel", "Airflow", "Argo_Workflows",
     "GitHub_Actions", "Tekton", "Splunk_SOAR", "n8n_NodeRED",
     "Temporal", "Flink_blocking", "Flink_pipelined", "Kafka_Streams",
     "Materialize", "Naiad_Timely", "GStreamer", "FFmpeg_filtergraph",
     "RxJS", "Frostbite_FrameGraph", "Erlang", "Akka", "Orleans",
     "Portals", "LangGraph_streaming", "LangGraph_batch"}

\* The encoding. Each entry is a 4-tuple
\* <<modality, invocation, topology, lifecycle>>.
SystemConfig ==
    [s \in SystemNames |->
      CASE s = "Bash_script"           ->
              <<"Sequential", "Manual",                  "None",                       "None">>
        [] s = "cron_job"              ->
              <<"Sequential", "Time",                    "None",                       "Rerun">>
        [] s = "GNU_parallel"          ->
              <<"ForkJoin",   "Manual",                  "None",                       "Sync_Barrier">>
        [] s = "MPI_scatter_gather"    ->
              <<"ForkJoin",   "Programmatic",            "None_Ranked",                "Sync_Barrier">>
        [] s = "MapReduce"             ->
              <<"ForkJoin",   "Programmatic",            "None",                       "Reexecute_Failed">>
        [] s = "Make"                  ->
              <<"StepGraph",  "Demand_Pull",             "Declared_DAG_File",          "Rerun_Changed">>
        [] s = "Bazel"                 ->
              <<"StepGraph",  "Demand_Pull",             "Declared_DAG_ContentHash",   "Incremental">>
        [] s = "Airflow"               ->
              <<"StepGraph",  "Time_Or_DepCompletion",   "Declared_DAG_Task",          "Rerun_From_Failure">>
        [] s = "Argo_Workflows"        ->
              <<"StepGraph",  "Event_Or_Programmatic",   "Declared_DAG",               "Rerun_From_Failure">>
        [] s = "GitHub_Actions"        ->
              <<"StepGraph",  "VCS_Event",               "Declared_DAG",               "Rerun_Job">>
        [] s = "Tekton"                ->
              <<"StepGraph",  "VCS_Or_Webhook",          "Declared_DAG",               "Rerun_Pipeline">>
        [] s = "Splunk_SOAR"           ->
              <<"StepGraph",  "Security_Event",          "Declared_Playbook",          "Per_Incident">>
        [] s = "n8n_NodeRED"           ->
              <<"StepGraph",  "HTTP_Or_Schedule",        "Declared_Visual_Flow",       "Per_Execution">>
        [] s = "Temporal"              ->
              <<"StepGraph_Cyclic", "Programmatic",      "Workflow_As_Code",           "Continuation_As_New">>
        [] s = "Flink_blocking"        ->
              <<"StepGraph",  "Programmatic",            "Declared_Anonymous",         "Checkpoint_Restart">>
        [] s = "Flink_pipelined"       ->
              <<"StreamGraph","Continuous",              "Declared_Anonymous",         "Checkpoint_Restart">>
        [] s = "Kafka_Streams"         ->
              <<"StreamGraph","Continuous",              "Declared_Topology",          "Per_Topology_Recovery">>
        [] s = "Materialize"           ->
              <<"StreamGraph","Continuous_Differential", "Declared_Incremental",       "Maintained_Views">>
        [] s = "Naiad_Timely"          ->
              <<"StreamGraph","Continuous_Progress",     "Declared_With_Iteration",    "Pointstamp_Based">>
        [] s = "GStreamer"             ->
              <<"StreamGraph","Continuous_Clock_Or_Sample","Declared_Element_Graph",   "Per_Pipeline">>
        [] s = "FFmpeg_filtergraph"    ->
              <<"StreamGraph","Continuous",              "Declared_Filter_Chain",      "Per_Invocation">>
        [] s = "RxJS"                  ->
              <<"StreamGraph","UI_Or_Data_Event",        "Declared_Observable_Chain",  "Subscription">>
        [] s = "Frostbite_FrameGraph"  ->
              <<"StreamGraph","Vsync",                   "Rebuilt_Per_Frame",          "Per_Frame">>
        [] s = "Erlang"                ->
              <<"StreamGraph","Message",                 "Dynamic_Addressable",        "Supervision_Tree">>
        [] s = "Akka"                  ->
              <<"StreamGraph","Message",                 "Dynamic_Addressable",        "Supervision">>
        [] s = "Orleans"               ->
              <<"StreamGraph","Message",                 "Virtual_Addressable",        "Persistence_Backed">>
        [] s = "Portals"               ->
              <<"StreamGraph","Message_Or_Continuous",   "Mixed_Declared_And_Dynamic", "Atomic_Stream">>
        [] s = "LangGraph_streaming"   ->
              <<"StreamGraph","PerToken_Or_PerMessage",  "Declared_Often_Cyclic",      "Per_Invocation">>
        [] s = "LangGraph_batch"       ->
              <<"StepGraph",  "Programmatic",            "Declared",                   "Per_Invocation">>
    ]

\* ----- Schema check -----

Modality(s)    == SystemConfig[s][1]
Invocation(s)  == SystemConfig[s][2]
Topology(s)    == SystemConfig[s][3]
Lifecycle(s)   == SystemConfig[s][4]

WellFormed(s) ==
    /\ Modality(s)   \in ModalityTags
    /\ Invocation(s) \in InvocationTags
    /\ Topology(s)   \in TopologyTags
    /\ Lifecycle(s)  \in LifecycleTags

AllWellFormed == \A s \in SystemNames : WellFormed(s)

\* ----- Modality-axis consistency rules -----
\* The modality boundaries imply constraints on the policy axes. The rules
\* below state them.

\* Rule: Sequential never has a topology (it has no graph).
SeqHasNoTopology ==
    \A s \in SystemNames :
        Modality(s) = "Sequential" => Topology(s) = "None"

\* Rule: ForkJoin never declares a topology; the absence of a topology is
\* structurally load-bearing.
ForkJoinHasNoTopology ==
    \A s \in SystemNames :
        Modality(s) = "ForkJoin" =>
            Topology(s) \in {"None", "None_Ranked"}

\* Rule: StepGraph always has some declared topology.
StepGraphHasTopology ==
    \A s \in SystemNames :
        (Modality(s) = "StepGraph" \/ Modality(s) = "StepGraph_Cyclic") =>
            Topology(s) \notin {"None", "None_Ranked"}

\* Rule: StreamGraph always has some declared or dynamic topology.
StreamGraphHasTopology ==
    \A s \in SystemNames :
        Modality(s) = "StreamGraph" =>
            Topology(s) \notin {"None", "None_Ranked"}

ModalityAxisConsistency ==
    /\ SeqHasNoTopology
    /\ ForkJoinHasNoTopology
    /\ StepGraphHasTopology
    /\ StreamGraphHasTopology

\* ----- Trivial state machine to satisfy TLC -----
VARIABLES checked

Init    == checked = FALSE
NextStep == checked' = TRUE
Next    == NextStep \/ (checked /\ UNCHANGED checked)
Spec    == Init /\ [][Next]_<<checked>>
====
