------------------------ MODULE AuditSinkDecomposed -------------------------
(* Decomposition of audit sink: separates append from hash computation.
   Concurrent append between AppendRecord and ComputeHash breaks the
   hash chain integrity. TLC finds ChainIntegrity violated.

   Uses a simple integer hash: hash(record, prev) = (record + prev) % Prime

   Two divergences from the module this unit names:
   - the invariant named ChainIntegrity below is stronger than canonical's.
     Its first conjunct is canonical HashBindsContent (modulo the
     operation->record field rename and a commuted argument order, which is
     sound only because this unit's Hash is commutative) and its second is
     canonical ChainIntegrity: two canonical obligations stated under the
     name canonical uses for the weaker one.  The conjunct that fires in both
     cold passes is the canonical-ChainIntegrity one.
   - canonical's `last_hash` variable is dropped (the chain tail is re-read
     from the log), which inverts the reference mechanism: there the
     two-phase writer leaves `last_hash` stale so the concurrent record
     captures the stale prev; here ConcurrentAppend recomputes from the
     true tail, and the stale prev lands on the two-phase writer's own
     entry.  Same defect class, opposite carrier.
   Canonical's MaxLogLen CONSTANT is the literal 4 in two action guards here,
   and the record field is `record` where canonical says `operation`.        *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Prime       \* e.g. 7
CONSTANT MaxRecord   \* e.g. 3
CONSTANT NULL

VARIABLE log, pending_record, pending_prev_hash, pc

vars == <<log, pending_record, pending_prev_hash, pc>>

Procs == {"p1", "p2"}

\* Simple hash function: (record + prev_hash) % Prime
Hash(record, prev) == (record + prev) % Prime

Init ==
    /\ log = <<>>
    /\ pending_record = [p \in Procs |-> 0]
    /\ pending_prev_hash = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "idle"]

(* Step 1: read current chain tail and prepare a record *)
AppendRecord(p) ==
    /\ pc[p] = "idle"
    /\ Len(log) < 4   \* bound the state space
    /\ \E r \in 1..MaxRecord :
        /\ pending_record' = [pending_record EXCEPT ![p] = r]
        /\ pending_prev_hash' = [pending_prev_hash EXCEPT ![p] =
            IF Len(log) > 0 THEN log[Len(log)].hash ELSE 0]
    /\ pc' = [pc EXCEPT ![p] = "hashing"]
    /\ UNCHANGED log

(* Step 2: compute hash and finalize the record *)
ComputeHash(p) ==
    /\ pc[p] = "hashing"
    /\ LET h == Hash(pending_record[p], pending_prev_hash[p])
           entry == [record |-> pending_record[p],
                     prev_hash |-> pending_prev_hash[p],
                     hash |-> h]
       IN log' = Append(log, entry)
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<pending_record, pending_prev_hash>>

(* Concurrent append: another process appends a full record atomically,
   interleaving with the first process's two-phase protocol *)
ConcurrentAppend(p) ==
    /\ pc[p] = "idle"
    /\ Len(log) < 4
    /\ \E r \in 1..MaxRecord :
        LET prev == IF Len(log) > 0 THEN log[Len(log)].hash ELSE 0
            h == Hash(r, prev)
            entry == [record |-> r, prev_hash |-> prev, hash |-> h]
        IN log' = Append(log, entry)
    /\ UNCHANGED <<pending_record, pending_prev_hash, pc>>

Next ==
    \E p \in Procs :
        \/ AppendRecord(p)
        \/ ComputeHash(p)
        \/ ConcurrentAppend(p)

(* Chain integrity, BOTH conjuncts: each entry's hash binds its own content,
   and each entry's prev_hash matches its predecessor's hash.  The first
   conjunct cannot fail in this model -- ComputeHash and ConcurrentAppend
   each construct every entry from that same equation -- so what this
   instrument witnesses is the second, which is canonical ChainIntegrity. *)
ChainIntegrity ==
    \A i \in 1..Len(log) :
        /\ log[i].hash = Hash(log[i].record, log[i].prev_hash)
        /\ (i > 1 => log[i].prev_hash = log[i-1].hash)

Spec == Init /\ [][Next]_vars
=============================================================================
