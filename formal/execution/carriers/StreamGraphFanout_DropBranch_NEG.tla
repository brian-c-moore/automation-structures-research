---- MODULE StreamGraphFanout_DropBranch_NEG ----
\* Per-branch conservation control. The broadcast appends only to the left
\* queue while still counting one ingested record, so the right branch loses
\* its required copy. Typing and both capacity bounds remain intact.

EXTENDS StreamGraphFanout

DropBranchIngest ==
    /\ ingested < MaxInputs
    /\ Len(left_queue) < Capacity
    /\ Len(right_queue) < Capacity
    /\ \E v \in RecordDomain : left_queue' = Append(left_queue, v)
    /\ right_queue' = right_queue
    /\ ingested' = ingested + 1
    /\ UNCHANGED <<left_emitted, right_emitted>>

BadWork == DropBranchIngest \/ ConsumeLeft \/ ConsumeRight
BadNext == BadWork \/ DoneStuttering
BadSpec == Init /\ [][BadNext]_vars
====
