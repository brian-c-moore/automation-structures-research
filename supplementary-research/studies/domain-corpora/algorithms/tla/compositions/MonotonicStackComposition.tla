---- MODULE MonotonicStackComposition ----
\* ====================================================================
\* COMPOSITION REFINEMENT: Monotonic Stack
\*
\* Validates the composition taxonomy: the monotonic stack pattern is a
\* COMPOSITION, not a primitive.
\*
\* The model instantiates the canonical ResourceRegistry and states its
\* buffer, cursor, and projection connective behavior directly.
\*
\* ATTRIBUTION BOUNDARIES
\*   - The stack is NOT a ResourceRegistry. A positionally-indexed buffer
\*     of pending items is not a unique key->value mapping, so it carries
\*     no governance obligation; it is the connective form Buffer.
\*   - The eviction step is NOT an ActuationPass, and the answer emission
\*     is NOT a Reduction: the eviction writes one answer for one index,
\*     which is the registry's own Register operation, and nothing is
\*     folded under an associative operator. The decomposition names one
\*     primitive.
\*
\* THE DECOMPOSITION
\*   Primitive:   ResourceRegistry<index -> answer>, INSTANCEd from the
\*                canonical module and carrying its own UniqueMapping
\*                obligation unchanged (RegistrySafety below), so the
\*                composition's state is a legal registry state at every
\*                step.
\*   Connectives: Buffer   -- stk, the pending indices, taken at one end
\*                Cursor   -- cur_idx, the position into the input
\*                Projection -- Answer(i), the derived read of the registry
\*   Given:       atomicity (evict-and-register commits in one step)
\*   Domain:      N, Vals, Sentinel, and the monotone comparison itself
\*
\* Abstract spec
\*   Input sequence Vals of length N.
\*   For each position i, AbstractAns(i) = the smallest j > i with
\*   Vals[j] > Vals[i], or Sentinel (0) if no such j exists.
\*   (Next-greater-element problem, the composition taxonomy.)
\*
\* Input (fixed in spec for TLC; N and values chosen to exercise all cases):
\*   N = 4, Vals = <<3, 1, 4, 2>>
\*   AbstractAns(1) = 3  (Vals[3]=4 > Vals[1]=3, next greater of 3 is 4 at idx 3)
\*   AbstractAns(2) = 3  (Vals[3]=4 > Vals[2]=1)
\*   AbstractAns(3) = 0  (no element after 4 is greater)
\*   AbstractAns(4) = 0  (no element after last)
\*
\* Refinement claim: every emitted concrete answer equals the abstract.
\* Expected outcome: PASS.
\*
\* Cross-tree resolution: the canonical primitive module is resolved through
\* the verification runner's TLA module search path. No copy is vendored here.
\* ====================================================================
EXTENDS Naturals, Sequences, FiniteSets

\* ── Input (fixed; not a CONSTANT to keep cfg simple) ──────────────────────────
\* Input sequence: Vals[1]=3, Vals[2]=1, Vals[3]=4, Vals[4]=2
N    == 4
Vals == <<3, 1, 4, 2>>

\* Sentinel: "no next greater element"
Sentinel == 0

\* ── Abstract answer ───────────────────────────────────────────────────────────
AbstractAns(i) ==
    LET candidates == { j \in 1..N : j > i /\ Vals[j] > Vals[i] }
    IN IF candidates = {}
       THEN Sentinel
       ELSE CHOOSE j \in candidates : \A j2 \in candidates : j <= j2

\* ── State variables ───────────────────────────────────────────────────────────
VARIABLES
    ab_ans,      \* abstract: answer array (1..N -> 0..N)
    ab_done,     \* abstract: set of positions finalized
    entries,     \* ResourceRegistry component state: {<<index, answer>>}
    stk,         \* connective (Buffer): pending indices, taken at one end
    cur_idx      \* connective (Cursor): position into Vals

vars == <<ab_ans, ab_done, entries, stk, cur_idx>>

\* ── The composed primitive ───────────────────────────────────────────────────
\* Variable names match, so the instance binds `entries` directly. It drives
\* the answer writes (Register) and carries the registry's own obligation
\* unchanged.
Registry == INSTANCE ResourceRegistry WITH Keys <- 1..N, Values <- 0..N

RegistrySafety == Registry!UniqueMapping

\* ── Projection: the derived read of the registry ──────────────────────────────
\* Stores nothing of its own. An index with no entry reads as Sentinel, which
\* is also the value a drained index is registered with, so the projection is
\* total over 1..N.
Answer(i) ==
    IF \E v \in 0..N : <<i, v>> \in entries
    THEN CHOOSE v \in 0..N : <<i, v>> \in entries
    ELSE Sentinel

\* ── Type invariant ────────────────────────────────────────────────────────────
TypeInvariant ==
    /\ ab_ans   \in [1..N -> 0..N]
    /\ ab_done  \subseteq 1..N
    /\ Registry!TypeInvariant
    /\ stk      \in Seq(1..N)
    /\ cur_idx  \in 1..(N+1)

\* ── Init ──────────────────────────────────────────────────────────────────────
Init ==
    /\ ab_ans   = [i \in 1..N |-> Sentinel]
    /\ ab_done  = {}
    /\ Registry!Init
    /\ stk      = <<>>
    /\ cur_idx  = 1

\* ── Abstract step: finalize answer for one position ──────────────────────────
AbsAnswer(i) ==
    /\ i \in 1..N
    /\ i \notin ab_done
    /\ ab_ans'  = [ab_ans  EXCEPT ![i] = AbstractAns(i)]
    /\ ab_done' = ab_done \cup {i}
    /\ UNCHANGED <<entries, stk, cur_idx>>

\* ── Evict one buffered index that the incoming value dominates ────────────────
\* The buffer take and the registry Register commit in one step (the
\* atomicity given), exactly as TraversalBudgetComposition fuses visit+deduct.
EvictTop ==
    /\ cur_idx <= N
    /\ Len(stk) > 0
    /\ Vals[stk[Len(stk)]] < Vals[cur_idx]
    /\ LET top == stk[Len(stk)]
       IN /\ stk' = SubSeq(stk, 1, Len(stk) - 1)
          /\ Registry!Register(top, cur_idx)
    /\ UNCHANGED <<ab_ans, ab_done, cur_idx>>

\* ── Buffer the current index and advance the cursor ───────────────────────────
\* Pure connective material: no component state changes.
PushCur ==
    /\ cur_idx <= N
    /\ IF Len(stk) = 0
       THEN TRUE
       ELSE Vals[stk[Len(stk)]] >= Vals[cur_idx]
    /\ stk'     = Append(stk, cur_idx)
    /\ cur_idx' = cur_idx + 1
    /\ UNCHANGED <<ab_ans, ab_done, entries>>

\* ── Drain the buffer once the input is consumed: each survivor gets Sentinel ──
DrainTop ==
    /\ cur_idx > N
    /\ Len(stk) > 0
    /\ LET top == stk[Len(stk)]
       IN /\ stk' = SubSeq(stk, 1, Len(stk) - 1)
          /\ Registry!Register(top, Sentinel)
    /\ UNCHANGED <<ab_ans, ab_done, cur_idx>>

\* ── Stutter ───────────────────────────────────────────────────────────────────
AllDone == ab_done = (1..N) /\ cur_idx > N /\ stk = <<>>

Stutter == AllDone /\ UNCHANGED vars

\* ── Next / Spec ───────────────────────────────────────────────────────────────
Next ==
    \/ \E i \in 1..N : AbsAnswer(i)
    \/ EvictTop
    \/ PushCur
    \/ DrainTop
    \/ Stutter

Spec == Init /\ [][Next]_vars

\* ── Refinement mapping ────────────────────────────────────────────────────────
\* Once all input is processed and the buffer drained, each concrete answer
\* equals the abstract answer.  (Intermediate states may be partial.)
RefinementHolds ==
    \A i \in 1..N :
        (cur_idx > N /\ stk = <<>>) =>
        Answer(i) = AbstractAns(i)

\* ── Additional safety invariants ──────────────────────────────────────────────

\* Buffer values are non-increasing bottom-to-top. EMERGENT from the eviction
\* discipline, not a policed obligation: a non-monotone buffer is still a
\* well-formed buffer, and what breaks is the surrounding composition's answers.
\* Guard on Len >= 2 avoids Naturals underflow when stk is empty.
StackMonotone ==
    Len(stk) >= 2 =>
        \A j \in 1..(Len(stk) - 1) :
            Vals[stk[j]] >= Vals[stk[j+1]]

\* Buffered indices are all in the already-processed range. Also emergent.
StackIndicesValid ==
    \A j \in 1..Len(stk) : stk[j] < cur_idx

\* Abstract answers are consistent with the abstract function.
AbstractConsistency ==
    \A i \in ab_done : ab_ans[i] = AbstractAns(i)

\* Concrete answers, once registered as non-Sentinel, agree with the abstract.
AnswerStability ==
    \A i \in 1..N :
        Answer(i) /= Sentinel =>
        Answer(i) = AbstractAns(i)

====
