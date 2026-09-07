---- MODULE BazelBehavior ----
\* ====================================================================
\* BAZEL BEHAVIORAL SPEC (bounded study configuration)
\*
\* Behavioral property under the StepGraph modality state machine:
\* Bazel rebuilds only when an input's content hash changes, not when
\* its timestamp changes. This is what distinguishes Bazel from Make
\* (which uses timestamps).
\*
\* State machine:
\*   - inputs carry both a `hash` and a `mtime` (modeled as integers).
\*   - external events bump mtime (touch), or change content (which
\*     changes hash). A "touch without content change" leaves hash
\*     unchanged.
\*   - `RunBazel` rebuilds the dependent target only if at least one
\*     input's hash differs from the hash captured at the previous
\*     rebuild (`last_built_hash`). Timestamp changes alone do not
\*     trigger a rebuild.
\*
\* Invariant `ContentHashedRebuilds` is an action property: rebuild_count
\* increases in a step only when some input's hash differs from the
\* hash recorded at the previous build.
\* ====================================================================
EXTENDS Naturals, FiniteSets

CONSTANTS Inputs, MaxRuns, MaxHash, MaxMtime

VARIABLES hash, mtime, last_built_hash, rebuild_count, runs

vars == <<hash, mtime, last_built_hash, rebuild_count, runs>>

TypeInvariant ==
    /\ hash            \in [Inputs -> 0..MaxHash]
    /\ mtime           \in [Inputs -> 0..MaxMtime]
    /\ last_built_hash \in [Inputs -> 0..MaxHash]
    /\ rebuild_count   \in 0..MaxRuns
    /\ runs            \in 0..MaxRuns

Init ==
    /\ hash            = [i \in Inputs |-> 0]
    /\ mtime           = [i \in Inputs |-> 0]
    /\ last_built_hash = [i \in Inputs |-> 0]
    /\ rebuild_count   = 0
    /\ runs            = 0

\* Touch: timestamp moves; content unchanged. Should NOT trigger rebuild.
Touch(i) ==
    /\ runs < MaxRuns
    /\ mtime[i] < MaxMtime
    /\ mtime' = [mtime EXCEPT ![i] = mtime[i] + 1]
    /\ UNCHANGED <<hash, last_built_hash, rebuild_count, runs>>

\* Edit: content changes; hash advances.
Edit(i) ==
    /\ runs < MaxRuns
    /\ hash[i] < MaxHash
    /\ mtime[i] < MaxMtime
    /\ hash'  = [hash  EXCEPT ![i] = hash[i] + 1]
    /\ mtime' = [mtime EXCEPT ![i] = mtime[i] + 1]
    /\ UNCHANGED <<last_built_hash, rebuild_count, runs>>

\* Build: rebuild iff at least one input has a hash different from the
\* hash captured at the previous build.
RunBazel ==
    /\ runs < MaxRuns
    /\ runs' = runs + 1
    /\ IF \E i \in Inputs : hash[i] # last_built_hash[i]
       THEN /\ rebuild_count'   = rebuild_count + 1
            /\ last_built_hash' = hash
       ELSE UNCHANGED <<rebuild_count, last_built_hash>>
    /\ UNCHANGED <<hash, mtime>>

DoneStuttering == runs >= MaxRuns /\ UNCHANGED vars

Next ==
    \/ \E i \in Inputs : Touch(i)
    \/ \E i \in Inputs : Edit(i)
    \/ RunBazel
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* ----- BEHAVIORAL INVARIANT -----
\* If rebuild_count increases by one in a step, at least one input's
\* hash differs from the recorded last_built_hash. A `Touch` (which
\* changes only mtime) cannot trigger a rebuild.
ContentHashedRebuilds ==
    [][rebuild_count' = rebuild_count + 1 =>
        \E i \in Inputs : hash[i] # last_built_hash[i]]_vars
====
