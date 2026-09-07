---- MODULE AtomicityBridge_Proof ----
(***************************************************************************
  TLAPS proof of the abstract atomicity bridge. It establishes:

      RefinementThm == Spec => H!Spec

  i.e. every behaviour of the lock-protected split check/act/audit
  realization (AtomicityBridge), whose audit append happens in the same
  critical section as the act, is a behaviour of the merged-transition
  composition unit AtomicCheckActAuditComposition, instantiated as H with
  log <- MappedLog.

  It also proves the five configured invariants:
  TypeSafety, LockDisciplineSafety, CheckedImpliesGuardSafety,
  CeilingSafety, AuditSyncSafety.

  Invokers is arbitrary: no cardinality or finiteness assumption is used. The
  AuditSync Cardinality reasoning needs
  only that Staged is empty or a singleton, which the lock discipline
  forces, and FS_EmptySet/FS_Singleton carry finiteness and the cardinality
  value for those literal shapes. Cap is any natural (CapType); NoLock is
  outside Invokers (NoLockFresh). Both ASSUMEs are inherited from
  AtomicityBridge.

  Method: the inductive invariant

      Inv == TypeInvariant /\ Ceiling /\ LockDiscipline
             /\ CheckedImpliesGuard /\ AuditSync /\ LogControl

  where LogControl is the pc-log correspondence (a not-yet-audited invoker
  never appears in the log), which establishes the
  i \notin H!Committed guard of H!Op). The refinement mapping linearizes at
  the act step: Act(i) maps to H!Op(i) (the fused check/act/audit), every
  other action to an H-stutter, because MappedLog counts the at-most-one
  staged record. The at-most-one is the mutex (LockDiscipline); the
  single-valued CHOOSE over the mutex singleton is discharged by
  ChooseSingleton. No fairness on either side, so no WF transfer.
 ***************************************************************************)
EXTENDS AtomicityBridge, FiniteSetTheorems, TLAPS

(*-------------------------------------------------------------------------*)
(* The pc-log correspondence: an invoker that has not yet been audited      *)
(* (pc outside {audited, done}) does not appear anywhere in the log. This   *)
(* is what makes the H!Op guard i \notin H!Committed hold at the act step   *)
(* (the acting invoker is at "checked", so it is not yet logged) and is     *)
(* self-maintaining across the append at Audit (the appended invoker is     *)
(* exactly the one leaving the not-yet-audited class).                      *)
(*-------------------------------------------------------------------------*)
LogControl ==
    \A n \in Invokers :
        pc[n] \notin {"audited", "done"} => (\A k \in 1..Len(log) : log[k] # n)

Inv ==
    /\ TypeInvariant
    /\ Ceiling
    /\ LockDiscipline
    /\ CheckedImpliesGuard
    /\ AuditSync
    /\ LogControl

(*=========================================================================*)
(* Constant-level helper lemmas with empty proof contexts.                 *)
(*=========================================================================*)

\* CHOOSE-determinacy over a singleton: the linearization's single staged
\* record is picked deterministically.
LEMMA ChooseSingleton == \A z : (CHOOSE n \in {z} : TRUE) = z
  <1> TAKE z
  <1>1. \E n \in {z} : TRUE
    OBVIOUS
  <1>2. (CHOOSE n \in {z} : TRUE) \in {z}
    BY <1>1
  <1> QED BY <1>2

\* Set-builder congruence: two pc-shaped functions agreeing on the "acted"
\* predicate induce the same Staged set (used for stutter Staged' = Staged).
LEMMA StagedFnCong ==
  ASSUME NEW f, NEW g,
         \A n \in Invokers : (f[n] = "acted") <=> (g[n] = "acted")
  PROVE  {n \in Invokers : f[n] = "acted"} = {n \in Invokers : g[n] = "acted"}
  OBVIOUS

\* A single-index pc update whose old and new values are both # "acted"
\* leaves the "acted" predicate pointwise unchanged.
LEMMA ExceptNotActed ==
  ASSUME NEW i \in Invokers, pc \in [Invokers -> PCStates],
         NEW v, v # "acted", pc[i] # "acted"
  PROVE  \A n \in Invokers :
            ([pc EXCEPT ![i] = v][n] = "acted") <=> (pc[n] = "acted")
  <1> TAKE n \in Invokers
  <1>1. [pc EXCEPT ![i] = v][n] = IF n = i THEN v ELSE pc[n]
    BY i \in Invokers, n \in Invokers
  <1>2. CASE n = i
    BY <1>1, <1>2
  <1>3. CASE n # i
    BY <1>1, <1>3
  <1> QED BY <1>2, <1>3

\* The mutex: when the lock is held by h, no other invoker is inside the
\* critical section (LockDiscipline's else-branch; lock = h # NoLock since
\* h \in Invokers and NoLock \notin Invokers).
LEMMA HolderOnly ==
  ASSUME TypeInvariant, LockDiscipline, NEW h, lock = h, h \in Invokers,
         NEW j \in Invokers, j # h
  PROVE  pc[j] \notin CSStates
  <1>1. lock # NoLock
    BY NoLockFresh
  <1> QED BY <1>1 DEF LockDiscipline

(*=========================================================================*)
(* Inductive invariant: Init establishes it, Next preserves it.            *)
(*=========================================================================*)

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>idle. \A n \in Invokers : pc[n] = "idle"
    BY DEF Init
  <1>noact. \A n \in Invokers : pc[n] # "acted"
    BY <1>idle
  <1>emp. Staged = {}
    BY <1>noact DEF Staged
  <1>1. TypeInvariant
    BY CapType DEF Init, TypeInvariant, PCStates
  <1>ceil. Ceiling
    BY CapType DEF Init, Ceiling
  <1>2. LockDiscipline
    BY <1>idle DEF Init, LockDiscipline, CSStates
  <1>3. CheckedImpliesGuard
    BY <1>idle DEF CheckedImpliesGuard
  <1>4. AuditSync
    <2>1. Len(log) = 0
      BY DEF Init
    <2>2. Cardinality(Staged) = 0
      BY <1>emp, FS_EmptySet
    <2> QED BY <2>1, <2>2 DEF Init, AuditSync
  <1>5. LogControl
    <2>1. Len(log) = 0
      BY DEF Init
    <2> QED BY <2>1 DEF LogControl
  <1> QED BY <1>1, <1>ceil, <1>2, <1>3, <1>4, <1>5 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>c. /\ x \in Nat
        /\ Ceiling
        /\ log \in Seq(Invokers)
        /\ lock \in Invokers \cup {NoLock}
        /\ pc \in [Invokers -> PCStates]
        /\ LockDiscipline
        /\ CheckedImpliesGuard
        /\ AuditSync
        /\ LogControl
    BY DEF Inv, TypeInvariant
  <1>xnat. x \in Nat
    BY <1>c
  <1>xle. x <= Cap
    BY <1>c DEF Ceiling
  <1>lennat. Len(log) \in Nat
    BY <1>c
  \* ----- the [Next]_vars stutter -----
  <1>0. CASE UNCHANGED vars
    <2>1. x' = x /\ log' = log /\ lock' = lock /\ pc' = pc
      BY <1>0 DEF vars
    <2>2. Staged' = Staged
      BY <2>1 DEF Staged
    <2> QED BY <2>1, <2>2, <1>c
       DEF Inv, TypeInvariant, Ceiling, LockDiscipline, CheckedImpliesGuard,
           AuditSync, LogControl, CSStates
  \* ----- the six actions -----
  <1>1. CASE Next
    <2> SUFFICES ASSUME NEW i \in Invokers,
                        \/ Acquire(i) \/ CheckPass(i) \/ CheckFail(i)
                        \/ Act(i) \/ Audit(i) \/ Release(i)
                 PROVE  Inv'
      BY <1>1 DEF Next
    (*---------------------------------------------------------------------*)
    (* Acquire(i): idle -> has_lock; lock NoLock -> i; x, log unchanged.   *)
    (*---------------------------------------------------------------------*)
    <2>Acq. CASE Acquire(i)
      <3>e. /\ pc[i] = "idle" /\ lock = NoLock /\ lock' = i
            /\ pc' = [pc EXCEPT ![i] = "has_lock"]
            /\ x' = x /\ log' = log
        BY <2>Acq DEF Acquire
      <3>pcty. pc' \in [Invokers -> PCStates]
        BY <3>e, <1>c DEF PCStates
      \* before Acquire, lock = NoLock, so no invoker is in the CS.
      <3>none. \A j \in Invokers : pc[j] \notin CSStates
        BY <3>e, <1>c DEF LockDiscipline
      <3>ty. TypeInvariant' /\ Ceiling'
        BY <3>e, <3>pcty, <1>c DEF TypeInvariant, Ceiling
      <3>ld. LockDiscipline'
        <4>0. lock' = i /\ i # NoLock
          BY <3>e, NoLockFresh
        <4>1. pc'[i] \in CSStates
          BY <3>e, <1>c DEF CSStates
        <4>2. \A j \in Invokers : j # i => pc'[j] \notin CSStates
          <5> TAKE j \in Invokers
          <5> HAVE j # i
          <5>1. pc'[j] = pc[j]
            BY <3>e, <1>c
          <5> QED BY <5>1, <3>none
        <4> QED BY <4>0, <4>1, <4>2 DEF LockDiscipline
      <3>cig. CheckedImpliesGuard'
        \* no invoker is "checked" after Acquire (none was, i became has_lock)
        <4>1. \A j \in Invokers : pc'[j] # "checked"
          <5> TAKE j \in Invokers
          <5>1. CASE j = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE j # i
            BY <3>e, <1>c, <5>2, <3>none DEF CSStates
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1 DEF CheckedImpliesGuard
      <3>sg. Staged' = Staged
        <4>1. \A n \in Invokers : (pc'[n] = "acted") <=> (pc[n] = "acted")
          BY <3>e, <1>c, ExceptNotActed
        <4> QED BY <4>1, StagedFnCong DEF Staged
      <3>as. AuditSync'
        BY <3>e, <3>sg, <1>c DEF AuditSync
      <3>lc. LogControl'
        <4>1. \A n \in Invokers : pc'[n] \notin {"audited", "done"} => pc[n] \notin {"audited", "done"}
          <5> TAKE n \in Invokers
          <5>1. CASE n = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE n # i
            BY <3>e, <1>c, <5>2
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1, <3>e, <1>c DEF LogControl
      <3> QED BY <3>ty, <3>ld, <3>cig, <3>as, <3>lc DEF Inv
    (*---------------------------------------------------------------------*)
    (* CheckPass(i): has_lock -> checked; lock = i; x, log unchanged.      *)
    (*---------------------------------------------------------------------*)
    <2>CP. CASE CheckPass(i)
      <3>e. /\ pc[i] = "has_lock" /\ lock = i /\ x < Cap
            /\ pc' = [pc EXCEPT ![i] = "checked"]
            /\ x' = x /\ log' = log /\ lock' = lock
        BY <2>CP DEF CheckPass
      <3>pcty. pc' \in [Invokers -> PCStates]
        BY <3>e, <1>c DEF PCStates
      <3>hold. \A j \in Invokers : j # i => pc[j] \notin CSStates
        BY <3>e, <1>c, HolderOnly DEF TypeInvariant
      <3>ty. TypeInvariant' /\ Ceiling'
        BY <3>e, <3>pcty, <1>c DEF TypeInvariant, Ceiling
      <3>ld. LockDiscipline'
        <4>0. lock' = i /\ i # NoLock
          BY <3>e, NoLockFresh
        <4>1. pc'[i] \in CSStates
          BY <3>e, <1>c DEF CSStates
        <4>2. \A j \in Invokers : j # i => pc'[j] \notin CSStates
          <5> TAKE j \in Invokers
          <5> HAVE j # i
          <5>1. pc'[j] = pc[j]
            BY <3>e, <1>c
          <5> QED BY <5>1, <3>hold
        <4> QED BY <4>0, <4>1, <4>2 DEF LockDiscipline
      <3>cig. CheckedImpliesGuard'
        <4> SUFFICES ASSUME NEW n \in Invokers, pc'[n] = "checked"
                     PROVE  x' < Cap
          BY DEF CheckedImpliesGuard
        <4>1. CASE n = i
          BY <3>e, <4>1
        <4>2. CASE n # i
          <5>1. pc'[n] = pc[n]
            BY <3>e, <1>c, <4>2
          <5>2. pc[n] = "checked"
            BY <5>1
          <5> QED BY <5>2, <3>e, <1>c DEF CheckedImpliesGuard
        <4> QED BY <4>1, <4>2
      <3>sg. Staged' = Staged
        <4>1. \A n \in Invokers : (pc'[n] = "acted") <=> (pc[n] = "acted")
          BY <3>e, <1>c, ExceptNotActed
        <4> QED BY <4>1, StagedFnCong DEF Staged
      <3>as. AuditSync'
        BY <3>e, <3>sg, <1>c DEF AuditSync
      <3>lc. LogControl'
        <4>1. \A n \in Invokers : pc'[n] \notin {"audited", "done"} => pc[n] \notin {"audited", "done"}
          <5> TAKE n \in Invokers
          <5>1. CASE n = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE n # i
            BY <3>e, <1>c, <5>2
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1, <3>e, <1>c DEF LogControl
      <3> QED BY <3>ty, <3>ld, <3>cig, <3>as, <3>lc DEF Inv
    (*---------------------------------------------------------------------*)
    (* CheckFail(i): has_lock -> aborted; lock = i; x, log unchanged.      *)
    (*---------------------------------------------------------------------*)
    <2>CF. CASE CheckFail(i)
      <3>e. /\ pc[i] = "has_lock" /\ lock = i /\ x >= Cap
            /\ pc' = [pc EXCEPT ![i] = "aborted"]
            /\ x' = x /\ log' = log /\ lock' = lock
        BY <2>CF DEF CheckFail
      <3>pcty. pc' \in [Invokers -> PCStates]
        BY <3>e, <1>c DEF PCStates
      <3>hold. \A j \in Invokers : j # i => pc[j] \notin CSStates
        BY <3>e, <1>c, HolderOnly DEF TypeInvariant
      <3>ty. TypeInvariant' /\ Ceiling'
        BY <3>e, <3>pcty, <1>c DEF TypeInvariant, Ceiling
      <3>ld. LockDiscipline'
        <4>0. lock' = i /\ i # NoLock
          BY <3>e, NoLockFresh
        <4>1. pc'[i] \in CSStates
          BY <3>e, <1>c DEF CSStates
        <4>2. \A j \in Invokers : j # i => pc'[j] \notin CSStates
          <5> TAKE j \in Invokers
          <5> HAVE j # i
          <5>1. pc'[j] = pc[j]
            BY <3>e, <1>c
          <5> QED BY <5>1, <3>hold
        <4> QED BY <4>0, <4>1, <4>2 DEF LockDiscipline
      <3>cig. CheckedImpliesGuard'
        \* no invoker is "checked" after CheckFail (mutex: only i in CS, now aborted)
        <4>1. \A j \in Invokers : pc'[j] # "checked"
          <5> TAKE j \in Invokers
          <5>1. CASE j = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE j # i
            BY <3>e, <1>c, <5>2, <3>hold DEF CSStates
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1 DEF CheckedImpliesGuard
      <3>sg. Staged' = Staged
        <4>1. \A n \in Invokers : (pc'[n] = "acted") <=> (pc[n] = "acted")
          BY <3>e, <1>c, ExceptNotActed
        <4> QED BY <4>1, StagedFnCong DEF Staged
      <3>as. AuditSync'
        BY <3>e, <3>sg, <1>c DEF AuditSync
      <3>lc. LogControl'
        <4>1. \A n \in Invokers : pc'[n] \notin {"audited", "done"} => pc[n] \notin {"audited", "done"}
          <5> TAKE n \in Invokers
          <5>1. CASE n = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE n # i
            BY <3>e, <1>c, <5>2
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1, <3>e, <1>c DEF LogControl
      <3> QED BY <3>ty, <3>ld, <3>cig, <3>as, <3>lc DEF Inv
    (*---------------------------------------------------------------------*)
    (* Act(i): checked -> acted; lock = i; x -> x+1; log unchanged.        *)
    (* The x-incrementing action; Staged {} -> {i}.                         *)
    (*---------------------------------------------------------------------*)
    <2>Act. CASE Act(i)
      <3>e. /\ pc[i] = "checked" /\ lock = i /\ x' = x + 1
            /\ pc' = [pc EXCEPT ![i] = "acted"]
            /\ log' = log /\ lock' = lock
        BY <2>Act DEF Act
      <3>pcty. pc' \in [Invokers -> PCStates]
        BY <3>e, <1>c DEF PCStates
      <3>hold. \A j \in Invokers : j # i => pc[j] \notin CSStates
        BY <3>e, <1>c, HolderOnly DEF TypeInvariant
      <3>xlt. x < Cap
        BY <3>e, <1>c DEF CheckedImpliesGuard
      \* Staged is empty before the act (mutex, and i is at "checked").
      <3>emp. Staged = {}
        <4>1. \A j \in Invokers : pc[j] # "acted"
          <5> TAKE j \in Invokers
          <5>1. CASE j = i
            BY <3>e, <5>1
          <5>2. CASE j # i
            BY <3>hold, <5>2 DEF CSStates
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1 DEF Staged
      \* Staged is exactly {i} after the act.
      <3>sng. Staged' = {i}
        <4>1. pc'[i] = "acted"
          BY <3>e, <1>c
        <4>2. \A j \in Invokers : j # i => pc'[j] # "acted"
          <5> TAKE j \in Invokers
          <5> HAVE j # i
          <5>1. pc'[j] = pc[j]
            BY <3>e, <1>c
          <5> QED BY <5>1, <3>hold DEF CSStates
        <4> QED BY <4>1, <4>2 DEF Staged
      <3>ty. TypeInvariant' /\ Ceiling'
        <4>1. x' \in Nat /\ x' <= Cap
          BY <3>e, <3>xlt, <1>xnat, CapType
        <4> QED BY <3>e, <3>pcty, <4>1, <1>c DEF TypeInvariant, Ceiling
      <3>ld. LockDiscipline'
        <4>0. lock' = i /\ i # NoLock
          BY <3>e, NoLockFresh
        <4>1. pc'[i] \in CSStates
          BY <3>e, <1>c DEF CSStates
        <4>2. \A j \in Invokers : j # i => pc'[j] \notin CSStates
          <5> TAKE j \in Invokers
          <5> HAVE j # i
          <5>1. pc'[j] = pc[j]
            BY <3>e, <1>c
          <5> QED BY <5>1, <3>hold
        <4> QED BY <4>0, <4>1, <4>2 DEF LockDiscipline
      <3>cig. CheckedImpliesGuard'
        \* no invoker is "checked" after Act (mutex: only i in CS, now acted).
        <4>1. \A j \in Invokers : pc'[j] # "checked"
          <5> TAKE j \in Invokers
          <5>1. CASE j = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE j # i
            BY <3>e, <1>c, <5>2, <3>hold DEF CSStates
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1 DEF CheckedImpliesGuard
      <3>as. AuditSync'
        <4>1. Cardinality(Staged) = 0
          BY <3>emp, FS_EmptySet
        <4>2. Cardinality(Staged') = 1
          BY <3>sng, FS_Singleton
        <4>3. Len(log) = x
          BY <4>1, <1>c, <1>lennat DEF AuditSync
        <4> QED BY <3>e, <4>2, <4>3, <1>lennat, <1>xnat DEF AuditSync
      <3>lc. LogControl'
        <4>1. \A n \in Invokers : pc'[n] \notin {"audited", "done"} => pc[n] \notin {"audited", "done"}
          <5> TAKE n \in Invokers
          <5>1. CASE n = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE n # i
            BY <3>e, <1>c, <5>2
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1, <3>e, <1>c DEF LogControl
      <3> QED BY <3>ty, <3>ld, <3>cig, <3>as, <3>lc DEF Inv
    (*---------------------------------------------------------------------*)
    (* Audit(i): acted -> audited; lock = i; log -> Append(log,i); x same. *)
    (* Staged {i} -> {}; the append is the linearized record's step.        *)
    (*---------------------------------------------------------------------*)
    <2>Aud. CASE Audit(i)
      <3>e. /\ pc[i] = "acted" /\ lock = i /\ log' = Append(log, i)
            /\ pc' = [pc EXCEPT ![i] = "audited"]
            /\ x' = x /\ lock' = lock
        BY <2>Aud DEF Audit
      <3>pcty. pc' \in [Invokers -> PCStates]
        BY <3>e, <1>c DEF PCStates
      <3>hold. \A j \in Invokers : j # i => pc[j] \notin CSStates
        BY <3>e, <1>c, HolderOnly DEF TypeInvariant
      <3>len. Len(log') = Len(log) + 1
        BY <3>e, <1>c
      \* Staged is exactly {i} before the audit.
      <3>sng. Staged = {i}
        <4>1. \A j \in Invokers : j # i => pc[j] # "acted"
          BY <3>hold DEF CSStates
        <4> QED BY <3>e, <4>1 DEF Staged
      \* Staged is empty after (i left the "acted" class; no one else in CS).
      <3>emp. Staged' = {}
        <4>1. \A j \in Invokers : pc'[j] # "acted"
          <5> TAKE j \in Invokers
          <5>1. CASE j = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE j # i
            <6>1. pc'[j] = pc[j]
              BY <3>e, <1>c, <5>2
            <6> QED BY <6>1, <3>hold, <5>2 DEF CSStates
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1 DEF Staged
      <3>ty. TypeInvariant' /\ Ceiling'
        <4>1. log' \in Seq(Invokers)
          BY <3>e, <1>c
        <4> QED BY <3>e, <3>pcty, <4>1, <1>c DEF TypeInvariant, Ceiling
      <3>ld. LockDiscipline'
        <4>0. lock' = i /\ i # NoLock
          BY <3>e, NoLockFresh
        <4>1. pc'[i] \in CSStates
          BY <3>e, <1>c DEF CSStates
        <4>2. \A j \in Invokers : j # i => pc'[j] \notin CSStates
          <5> TAKE j \in Invokers
          <5> HAVE j # i
          <5>1. pc'[j] = pc[j]
            BY <3>e, <1>c
          <5> QED BY <5>1, <3>hold
        <4> QED BY <4>0, <4>1, <4>2 DEF LockDiscipline
      <3>cig. CheckedImpliesGuard'
        <4> SUFFICES ASSUME NEW n \in Invokers, pc'[n] = "checked"
                     PROVE  x' < Cap
          BY DEF CheckedImpliesGuard
        <4>1. n # i
          BY <3>e, <1>c
        <4>2. pc[n] = "checked"
          BY <3>e, <1>c, <4>1
        <4> QED BY <4>2, <3>e, <1>c DEF CheckedImpliesGuard
      <3>as. AuditSync'
        <4>1. Cardinality(Staged) = 1
          BY <3>sng, FS_Singleton
        <4>2. Cardinality(Staged') = 0
          BY <3>emp, FS_EmptySet
        <4>3. Len(log) + 1 = x
          BY <4>1, <1>c, <1>lennat DEF AuditSync
        <4> QED BY <3>e, <3>len, <4>2, <4>3, <1>lennat, <1>xnat DEF AuditSync
      <3>lc. LogControl'
        <4> SUFFICES ASSUME NEW n \in Invokers, pc'[n] \notin {"audited", "done"},
                            NEW k \in 1..Len(log')
                     PROVE  log'[k] # n
          BY DEF LogControl
        <4>ni. n # i
          BY <3>e, <1>c
        <4>pc. pc[n] = pc'[n] /\ pc[n] \notin {"audited", "done"}
          BY <3>e, <1>c, <4>ni
        <4>1. CASE k \in 1..Len(log)
          <5>1. log'[k] = log[k]
            BY <3>e, <1>c, <4>1
          <5>2. log[k] # n
            BY <4>pc, <4>1, <1>c DEF LogControl
          <5> QED BY <5>1, <5>2
        <4>2. CASE k = Len(log) + 1
          <5>1. log'[k] = i
            BY <3>e, <1>c, <4>2, <3>len
          <5> QED BY <5>1, <4>ni
        <4> QED BY <4>1, <4>2, <3>len, <1>lennat
      <3> QED BY <3>ty, <3>ld, <3>cig, <3>as, <3>lc DEF Inv
    (*---------------------------------------------------------------------*)
    (* Release(i): {audited,aborted} -> done; lock i -> NoLock; x,log same.*)
    (*---------------------------------------------------------------------*)
    <2>Rel. CASE Release(i)
      <3>e. /\ pc[i] \in {"audited", "aborted"} /\ lock = i /\ lock' = NoLock
            /\ pc' = [pc EXCEPT ![i] = "done"]
            /\ x' = x /\ log' = log
        BY <2>Rel DEF Release
      <3>pcty. pc' \in [Invokers -> PCStates]
        BY <3>e, <1>c DEF PCStates
      <3>hold. \A j \in Invokers : j # i => pc[j] \notin CSStates
        BY <3>e, <1>c, HolderOnly DEF TypeInvariant
      <3>ina. pc[i] # "acted"
        BY <3>e
      <3>ty. TypeInvariant' /\ Ceiling'
        BY <3>e, <3>pcty, <1>c DEF TypeInvariant, Ceiling
      <3>ld. LockDiscipline'
        \* lock' = NoLock, so the discipline needs everyone outside the CS.
        <4>1. \A j \in Invokers : pc'[j] \notin CSStates
          <5> TAKE j \in Invokers
          <5>1. CASE j = i
            BY <3>e, <1>c, <5>1 DEF CSStates
          <5>2. CASE j # i
            <6>1. pc'[j] = pc[j]
              BY <3>e, <1>c, <5>2
            <6> QED BY <6>1, <3>hold, <5>2
          <5> QED BY <5>1, <5>2
        <4> QED BY <3>e, <4>1 DEF LockDiscipline
      <3>cig. CheckedImpliesGuard'
        <4> SUFFICES ASSUME NEW n \in Invokers, pc'[n] = "checked"
                     PROVE  x' < Cap
          BY DEF CheckedImpliesGuard
        <4>1. n # i
          BY <3>e, <1>c
        <4>2. pc[n] = "checked"
          BY <3>e, <1>c, <4>1
        <4> QED BY <4>2, <3>e, <1>c DEF CheckedImpliesGuard
      <3>sg. Staged' = Staged
        <4>1. \A n \in Invokers : (pc'[n] = "acted") <=> (pc[n] = "acted")
          BY <3>e, <3>ina, <1>c, ExceptNotActed
        <4> QED BY <4>1, StagedFnCong DEF Staged
      <3>as. AuditSync'
        BY <3>e, <3>sg, <1>c DEF AuditSync
      <3>lc. LogControl'
        <4>1. \A n \in Invokers : pc'[n] \notin {"audited", "done"} => pc[n] \notin {"audited", "done"}
          <5> TAKE n \in Invokers
          <5>1. CASE n = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE n # i
            BY <3>e, <1>c, <5>2
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1, <3>e, <1>c DEF LogControl
      <3> QED BY <3>ty, <3>ld, <3>cig, <3>as, <3>lc DEF Inv
    <2> QED BY <2>Acq, <2>CP, <2>CF, <2>Act, <2>Aud, <2>Rel
  <1> QED BY <1>0, <1>1 DEF Next

(*-------------------------------------------------------------------------*)
(* Safety: the inductive invariant holds in every reachable state, and the  *)
(* five .cfg-checked invariants as corollaries.                             *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM LockDisciplineSafety == Spec => []LockDiscipline
  BY Safety, PTL DEF Inv

THEOREM CheckedImpliesGuardSafety == Spec => []CheckedImpliesGuard
  BY Safety, PTL DEF Inv

THEOREM AuditSyncSafety == Spec => []AuditSync
  BY Safety, PTL DEF Inv

THEOREM CeilingSafety == Spec => []Ceiling
  BY Safety, PTL DEF Inv

(*=========================================================================*)
(* The refinement: Init maps to H!Init; Act(i) maps to H!Op(i); every      *)
(* other action maps to an H-stutter. H is AtomicCheckActAuditComposition  *)
(* instantiated with log <- MappedLog.                                     *)
(*=========================================================================*)

LEMMA InitRefines == Init => H!Init
  <1> SUFFICES ASSUME Init PROVE H!Init
    OBVIOUS
  <1>1. \A n \in Invokers : pc[n] = "idle"
    BY DEF Init
  <1>2. Staged = {}
    <2>1. \A n \in Invokers : pc[n] # "acted"
      BY <1>1
    <2> QED BY <2>1 DEF Staged
  <1>3. MappedLog = <<>>
    BY <1>2 DEF Init, MappedLog
  <1>4. x = 0
    BY DEF Init
  <1> QED BY <1>3, <1>4 DEF H!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [H!Next]_(H!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [H!Next]_(H!vars)
    OBVIOUS
  <1>c. /\ x \in Nat
        /\ log \in Seq(Invokers)
        /\ lock \in Invokers \cup {NoLock}
        /\ pc \in [Invokers -> PCStates]
        /\ LockDiscipline
        /\ CheckedImpliesGuard
        /\ LogControl
    BY DEF Inv, TypeInvariant
  \* A uniform stutter closer: x' = x /\ MappedLog' = MappedLog gives the
  \* [_]_ right disjunct. Staged' = Staged (from a pointwise-unchanged
  \* "acted" predicate) and log' = log carry MappedLog across.
  <1>0. CASE UNCHANGED vars
    <2>1. x' = x /\ log' = log /\ pc' = pc
      BY <1>0 DEF vars
    <2>2. Staged' = Staged
      BY <2>1 DEF Staged
    <2>3. MappedLog' = MappedLog
      BY <2>1, <2>2 DEF MappedLog
    <2> QED BY <2>1, <2>3 DEF H!vars
  <1>1. CASE Next
    <2> SUFFICES ASSUME NEW i \in Invokers,
                        \/ Acquire(i) \/ CheckPass(i) \/ CheckFail(i)
                        \/ Act(i) \/ Audit(i) \/ Release(i)
                 PROVE  [H!Next]_(H!vars)
      BY <1>1 DEF Next
    (* -- the four pure stutters share the same closing shape -- *)
    <2>Acq. CASE Acquire(i)
      <3>e. /\ pc[i] = "idle" /\ pc' = [pc EXCEPT ![i] = "has_lock"]
            /\ x' = x /\ log' = log
        BY <2>Acq DEF Acquire
      <3>1. Staged' = Staged
        <4>1. \A n \in Invokers : (pc'[n] = "acted") <=> (pc[n] = "acted")
          BY <3>e, <1>c, ExceptNotActed
        <4> QED BY <4>1, StagedFnCong DEF Staged
      <3>2. MappedLog' = MappedLog
        BY <3>e, <3>1 DEF MappedLog
      <3> QED BY <3>e, <3>2 DEF H!vars
    <2>CP. CASE CheckPass(i)
      <3>e. /\ pc[i] = "has_lock" /\ pc' = [pc EXCEPT ![i] = "checked"]
            /\ x' = x /\ log' = log
        BY <2>CP DEF CheckPass
      <3>1. Staged' = Staged
        <4>1. \A n \in Invokers : (pc'[n] = "acted") <=> (pc[n] = "acted")
          BY <3>e, <1>c, ExceptNotActed
        <4> QED BY <4>1, StagedFnCong DEF Staged
      <3>2. MappedLog' = MappedLog
        BY <3>e, <3>1 DEF MappedLog
      <3> QED BY <3>e, <3>2 DEF H!vars
    <2>CF. CASE CheckFail(i)
      <3>e. /\ pc[i] = "has_lock" /\ pc' = [pc EXCEPT ![i] = "aborted"]
            /\ x' = x /\ log' = log
        BY <2>CF DEF CheckFail
      <3>1. Staged' = Staged
        <4>1. \A n \in Invokers : (pc'[n] = "acted") <=> (pc[n] = "acted")
          BY <3>e, <1>c, ExceptNotActed
        <4> QED BY <4>1, StagedFnCong DEF Staged
      <3>2. MappedLog' = MappedLog
        BY <3>e, <3>1 DEF MappedLog
      <3> QED BY <3>e, <3>2 DEF H!vars
    <2>Rel. CASE Release(i)
      <3>e. /\ pc[i] \in {"audited", "aborted"} /\ pc' = [pc EXCEPT ![i] = "done"]
            /\ x' = x /\ log' = log
        BY <2>Rel DEF Release
      <3>ina. pc[i] # "acted"
        BY <3>e
      <3>1. Staged' = Staged
        <4>1. \A n \in Invokers : (pc'[n] = "acted") <=> (pc[n] = "acted")
          BY <3>e, <3>ina, <1>c, ExceptNotActed
        <4> QED BY <4>1, StagedFnCong DEF Staged
      <3>2. MappedLog' = MappedLog
        BY <3>e, <3>1 DEF MappedLog
      <3> QED BY <3>e, <3>2 DEF H!vars
    (* -- the audit stutter: Staged {i} -> {}, but MappedLog counts the -- *)
    (* -- staged record already, so the append is a target stutter      -- *)
    <2>Aud. CASE Audit(i)
      <3>e. /\ pc[i] = "acted" /\ lock = i /\ log' = Append(log, i)
            /\ pc' = [pc EXCEPT ![i] = "audited"] /\ x' = x
        BY <2>Aud DEF Audit
      <3>hold. \A j \in Invokers : j # i => pc[j] \notin CSStates
        BY <3>e, <1>c, HolderOnly DEF TypeInvariant
      <3>sng. Staged = {i}
        <4>1. \A j \in Invokers : j # i => pc[j] # "acted"
          BY <3>hold DEF CSStates
        <4> QED BY <3>e, <4>1 DEF Staged
      <3>emp. Staged' = {}
        <4>1. \A j \in Invokers : pc'[j] # "acted"
          <5> TAKE j \in Invokers
          <5>1. CASE j = i
            BY <3>e, <1>c, <5>1
          <5>2. CASE j # i
            <6>1. pc'[j] = pc[j]
              BY <3>e, <1>c, <5>2
            <6> QED BY <6>1, <3>hold, <5>2 DEF CSStates
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1 DEF Staged
      \* MappedLog before = Append(log, i) (the staged record, linearized);
      \* MappedLog after = log' = Append(log, i). Equal, so H stutters.
      <3>ml. MappedLog = Append(log, i)
        <4>1. (CHOOSE n \in Staged : TRUE) = i
          <5>1. (CHOOSE n \in {i} : TRUE) = i
            BY ChooseSingleton
          <5> QED BY <3>sng, <5>1
        <4> QED BY <3>sng, <4>1 DEF MappedLog
      <3>ml2. MappedLog' = Append(log, i)
        BY <3>e, <3>emp DEF MappedLog
      <3>1. MappedLog' = MappedLog
        BY <3>ml, <3>ml2
      <3> QED BY <3>e, <3>1 DEF H!vars
    (* -- the act: the linearization point; maps to H!Op(i) -- *)
    <2>Act. CASE Act(i)
      <3>e. /\ pc[i] = "checked" /\ lock = i /\ x' = x + 1
            /\ pc' = [pc EXCEPT ![i] = "acted"] /\ log' = log
        BY <2>Act DEF Act
      <3>hold. \A j \in Invokers : j # i => pc[j] \notin CSStates
        BY <3>e, <1>c, HolderOnly DEF TypeInvariant
      <3>xlt. x < Cap
        BY <3>e, <1>c DEF CheckedImpliesGuard
      <3>emp. Staged = {}
        <4>1. \A j \in Invokers : pc[j] # "acted"
          <5> TAKE j \in Invokers
          <5>1. CASE j = i
            BY <3>e, <5>1
          <5>2. CASE j # i
            BY <3>hold, <5>2 DEF CSStates
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1 DEF Staged
      <3>sng. Staged' = {i}
        <4>1. pc'[i] = "acted"
          BY <3>e, <1>c
        <4>2. \A j \in Invokers : j # i => pc'[j] # "acted"
          <5> TAKE j \in Invokers
          <5> HAVE j # i
          <5>1. pc'[j] = pc[j]
            BY <3>e, <1>c
          <5> QED BY <5>1, <3>hold DEF CSStates
        <4> QED BY <4>1, <4>2 DEF Staged
      \* MappedLog before = log (Staged empty); MappedLog after =
      \* Append(log', i) = Append(log, i) (Staged' = {i}, CHOOSE = i).
      <3>mlpre. MappedLog = log
        BY <3>emp DEF MappedLog
      <3>mlpost. MappedLog' = Append(log, i)
        <4>1. (CHOOSE n \in Staged' : TRUE) = i
          <5>1. (CHOOSE n \in {i} : TRUE) = i
            BY ChooseSingleton
          <5> QED BY <3>sng, <5>1
        <4> QED BY <3>e, <3>sng, <4>1 DEF MappedLog
      \* the H!Op(i) guard: i is not yet in the log (it is at "checked").
      <3>dom. DOMAIN log = 1..Len(log)
        BY <1>c
      <3>gd. i \notin H!Committed
        <4>1. \A k \in 1..Len(log) : log[k] # i
          BY <3>e, <1>c DEF LogControl
        <4>2. i \notin {log[k] : k \in DOMAIN log}
          BY <4>1, <3>dom
        <4> QED BY <4>2, <3>mlpre DEF H!Committed
      <3>op. H!Op(i)
        <4>1. x' = x + 1
          BY <3>e
        <4>2. MappedLog' = Append(MappedLog, i)
          BY <3>mlpost, <3>mlpre
        <4> QED BY <3>gd, <3>xlt, <4>1, <4>2 DEF H!Op
      <3> QED BY <3>op DEF H!Next
    <2> QED BY <2>Acq, <2>CP, <2>CF, <2>Act, <2>Aud, <2>Rel
  <1> QED BY <1>0, <1>1 DEF Next

(*-------------------------------------------------------------------------*)
(* The critical section refines the merged-transition composition unit.    *)
(*-------------------------------------------------------------------------*)
THEOREM RefinementThm == Spec => H!Spec
  <1>1. Init => H!Init
    BY InitRefines
  <1>2. Inv /\ [Next]_vars => [H!Next]_(H!vars)
    BY NextRefines
  <1>3. Spec => []Inv
    BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, H!Spec

\* Restatement in the base module's own vocabulary (Refinement == H!Spec).
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement

====
