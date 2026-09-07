---- MODULE MonotonicDequeComposition ----
\* ====================================================================
\* COMPOSITION REFINEMENT: Monotonic Deque / Sliding Window Maximum
\*
\* Sibling of MonotonicStackComposition, sharing its decomposition shape.
\* Validates the algorithm corpus: Sliding Window Maximum is a composition
\* pattern (not a primitive).
\*
\* The model instantiates the canonical ResourceRegistry and states its
\* double-ended buffer, cursor, and projection behavior directly.
\*
\* ATTRIBUTION BOUNDARIES
\*   - The deque is NOT a ResourceRegistry. It holds pending indices and
\*     is taken from at both ends; a positional buffer is not a unique
\*     key->value mapping and carries no governance obligation. It is the
\*     connective form Buffer, in its double-ended variant.
\*   - Neither eviction is an ActuationPass: nothing is applied to an
\*     actuation scope, an item is taken from an end.
\*   - The window maximum is NOT a Reduction. It is never folded: the
\*     eviction discipline keeps the maximum at the front, so emission is
\*     a single read.
\*
\* THE DECOMPOSITION
\*   Primitive:   ResourceRegistry<window -> maximum>, INSTANCEd from the
\*                canonical module and carrying its UniqueMapping
\*                obligation unchanged (RegistrySafety below).
\*   Connectives: Buffer     -- dq, pending indices, taken at either end
\*                Cursor     -- cur_pos, the position into the input
\*                Projection -- the front read, and WinMax(i) over the registry
\*   Given:       atomicity (append-and-emit commits in one step)
\*   Domain:      N, K, Vals, and the comparisons themselves
\*
\* Abstract spec
\*   Input sequence Vals of length N, window size K.
\*   For each window start i in 1..(N-K+1):
\*     AbstractWinMax(i) = max{ Vals[j] : i <= j <= i+K-1 }.
\*
\* Input (N=5, K=3, Vals=<<5,4,1,3,2>>):
\*   Window 1 (idx 1..3): max(5,4,1)=5
\*   Window 2 (idx 2..4): max(4,1,3)=4
\*   Window 3 (idx 3..5): max(1,3,2)=3
\* Three DISTINCT maxima, and the maximum leaves the window twice. The input
\* has to be non-degenerate: windows that all share one maximum cannot
\* distinguish a correct implementation from one that always emits that
\* value. This input exercises both eviction paths — the front eviction
\* fires when the window's maximum leaves the window, and the back eviction
\* fires when a larger element arrives and dominates buffered ones.
\*
\* Refinement claim: every concrete window answer equals the abstract.
\* Expected outcome: PASS.
\*
\* Cross-tree resolution: the canonical primitive module is resolved through
\* the verification runner's TLA module search path. No copy is vendored here.
\* ====================================================================
EXTENDS Naturals, Sequences, FiniteSets

\* ── Input (fixed; not CONSTANTS to keep cfg simple) ──────────────────────────
N == 5
K == 3
\* Non-degenerate by construction: the three window maxima are 5, 4, 3 -- all
\* distinct -- and both eviction paths are exercised.
Vals == <<5, 4, 1, 3, 2>>

\* Number of windows
NumWindows == N - K + 1   \* = 3

\* ── Abstract window maximum ───────────────────────────────────────────────────
AbstractWinMax(i) ==
    LET window == { Vals[j] : j \in i..(i + K - 1) }
    IN CHOOSE m \in window : \A v \in window : m >= v

\* ── Projections over the buffer's ends ────────────────────────────────────────
DqFront(dq) == dq[1]
DqBack(dq)  == dq[Len(dq)]

\* ── State variables ───────────────────────────────────────────────────────────
VARIABLES
    ab_win,      \* abstract: array 1..NumWindows -> Nat (window maxima)
    ab_done,     \* abstract: set of window indices finalized
    entries,     \* ResourceRegistry component state: {<<window, maximum>>}
    dq,          \* connective (Buffer): pending indices, taken at either end
    cur_pos      \* connective (Cursor): input position being ingested

vars == <<ab_win, ab_done, entries, dq, cur_pos>>

\* ── The composed primitive ───────────────────────────────────────────────────
Registry == INSTANCE ResourceRegistry WITH Keys <- 1..NumWindows, Values <- 0..N

RegistrySafety == Registry!UniqueMapping

\* ── Projection: the derived read of the registry ──────────────────────────────
\* A window with no entry reads as 0, the "unset" value the abstract array
\* used, so the projection is total over 1..NumWindows.
WinMax(i) ==
    IF \E v \in 0..N : <<i, v>> \in entries
    THEN CHOOSE v \in 0..N : <<i, v>> \in entries
    ELSE 0

\* ── Type invariant ────────────────────────────────────────────────────────────
TypeInvariant ==
    /\ ab_win   \in [1..NumWindows -> 0..N]
    /\ ab_done  \subseteq 1..NumWindows
    /\ Registry!TypeInvariant
    /\ dq       \in Seq(1..N)
    /\ cur_pos  \in 1..(N+1)

\* ── Init ──────────────────────────────────────────────────────────────────────
Init ==
    /\ ab_win   = [i \in 1..NumWindows |-> 0]
    /\ ab_done  = {}
    /\ Registry!Init
    /\ dq       = <<>>
    /\ cur_pos  = 1

\* ── Abstract step: finalize one window answer ────────────────────────────────
AbsWindow(i) ==
    /\ i \in 1..NumWindows
    /\ i \notin ab_done
    /\ ab_win'  = [ab_win  EXCEPT ![i] = AbstractWinMax(i)]
    /\ ab_done' = ab_done \cup {i}
    /\ UNCHANGED <<entries, dq, cur_pos>>

\* ── Take from the back: the incoming value dominates it ───────────────────────
\* Pure connective material: no component state changes.
EvictBack ==
    /\ cur_pos <= N
    /\ Len(dq) > 0
    /\ Vals[DqBack(dq)] <= Vals[cur_pos]
    /\ dq' = SubSeq(dq, 1, Len(dq) - 1)
    /\ UNCHANGED <<ab_win, ab_done, entries, cur_pos>>

\* ── Take from the front: it has left the window ───────────────────────────────
\* Front is outside window when its index < cur_pos - K + 1. Also pure glue.
EvictFront ==
    /\ cur_pos <= N
    /\ Len(dq) > 0
    /\ cur_pos >= K        \* guard: ensures cur_pos - K + 1 >= 1 (no Naturals underflow)
    /\ DqFront(dq) < cur_pos - K + 1
    /\ dq' = SubSeq(dq, 2, Len(dq))
    /\ UNCHANGED <<ab_win, ab_done, entries, cur_pos>>

\* ── Append the current index, and register the window maximum if one closes ───
\* Push when: back is not dominated (or deque empty) AND front is in window
\* (or empty). After the push, if cur_pos >= K a full window exists, and its
\* maximum is the front read — the buffer append and the registry Register
\* commit in one step (the atomicity given).
PushCur ==
    /\ cur_pos <= N
    /\ IF Len(dq) = 0
       THEN TRUE
       ELSE Vals[DqBack(dq)] > Vals[cur_pos]
    /\ IF Len(dq) = 0 \/ cur_pos < K
       THEN TRUE
       ELSE DqFront(dq) >= cur_pos - K + 1
    /\ LET new_dq == Append(dq, cur_pos)
       IN /\ dq' = new_dq
          /\ IF cur_pos >= K
             THEN Registry!Register(cur_pos - K + 1, Vals[DqFront(new_dq)])
             ELSE UNCHANGED entries
    /\ cur_pos' = cur_pos + 1
    /\ UNCHANGED <<ab_win, ab_done>>

\* ── Stutter ───────────────────────────────────────────────────────────────────
AllDone == ab_done = (1..NumWindows) /\ cur_pos > N

Stutter == AllDone /\ UNCHANGED vars

\* ── Next / Spec ───────────────────────────────────────────────────────────────
Next ==
    \/ \E i \in 1..NumWindows : AbsWindow(i)
    \/ EvictBack
    \/ EvictFront
    \/ PushCur
    \/ Stutter

Spec == Init /\ [][Next]_vars

\* ── Refinement mapping ────────────────────────────────────────────────────────
\* Once cur_pos has advanced past the end of window i (i.e., cur_pos > i+K-1),
\* the concrete answer for window i must equal the abstract answer.
RefinementHolds ==
    \A i \in 1..NumWindows :
        cur_pos > i + K - 1 =>
        WinMax(i) = AbstractWinMax(i)

\* ── Additional safety invariants ──────────────────────────────────────────────

\* Buffer values strictly decreasing front-to-back. EMERGENT from the eviction
\* discipline, not a policed obligation: a non-monotone buffer is still a
\* well-formed buffer, and what breaks is the surrounding composition's answers.
DequeMonotone ==
    Len(dq) >= 2 =>
        \A j \in 1..(Len(dq) - 1) :
            Vals[dq[j]] > Vals[dq[j+1]]

\* All buffered indices are in the already-processed range. Also emergent.
DequeIndicesValid ==
    \A j \in 1..Len(dq) : dq[j] < cur_pos

\* Front index, if present, has not yet expired. Also emergent.
\* Guard on cur_pos > K avoids Natural underflow when cur_pos < K.
FrontInWindow ==
    (Len(dq) > 0 /\ cur_pos > K) =>
        DqFront(dq) >= cur_pos - K

\* Abstract answers are correct.
AbstractConsistency ==
    \A i \in ab_done : ab_win[i] = AbstractWinMax(i)

====
