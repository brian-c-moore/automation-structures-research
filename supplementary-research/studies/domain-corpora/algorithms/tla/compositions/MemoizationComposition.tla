---- MODULE MemoizationComposition ----
\* ====================================================================
\* COMPOSITION REFINEMENT: Memoization
\*
\* Memoization is a composition pattern, not a primitive.
\*
\* The memo table is the canonical ResourceRegistry, INSTANCEd from the
\* canonical module: the upsert is Registry!Register, the initial state is
\* Registry!Init, and UniqueMapping is the component's own obligation.
\*
\* The canonical TraversalEngine and Reduction modules fix their domain as a
\* CONSTANT -- TraversalEngine's topology is hardcoded, and Reduction's Items
\* set is constant with Init setting remaining = Items. This composition walks
\* an input graph and runs one fold per cell, and TLA+ offers no way to re-arm
\* an INSTANCE with a fresh domain, so neither can be bound. The traversal and
\* the per-cell aggregation are expressed inline.
\*
\* Inline state, by connective form:
\*   tq_queue     -- pending ready keys: a buffer
\*   tq_visited   -- recorded designations consulted by later guards: markers
\*   rd_key       -- the cell currently aggregating, consulted by later guards
\*   rd_remaining -- the predecessors not yet folded: a buffer
\*   rd_accum     -- the running partial carried across steps: an accumulator
\*   IsMemoized / MemoVal / AllPredsIn / Predecessors / Successors / the
\*                ready-set derivation -- projections, storing nothing
\* The inline aggregation is a hand-threaded fold, not a realization of the
\* canonical Reduction carrier.
\*
\* Abstract spec
\*   f : Keys -> Nat with a fixed dependency relation DepRel over Keys.
\*   <<p, k>> in DepRel means k depends on p (p is a predecessor of k).
\*   The dependency graph is a DAG; cells are filled in topological order.
\*   f(k) = BaseVal + StepVal * |Predecessors(k)|  (linear recurrence).
\*
\* Topology (defined here so the .cfg only needs simple model values):
\*   Keys = {k1, k2, k3, k4}
\*   DepRel: k1->k2, k1->k3, k2->k4, k3->k4   (diamond shape)
\*
\* Concrete spec:
\*   ResourceRegistry -- the memo table, INSTANCEd from the canonical module.
\*   A topological fill over the dependency DAG, and a per-cell aggregate
\*   of StepVal per predecessor from BaseVal, both expressed inline and named
\*   in the list above.
\*
\* Value range: BaseVal=1, StepVal=1, max predecessors=2 => max value=3.
\*   ValRange = 0..10 is generous; keeps all sets finite for TLC.
\*
\* Refinement claim: every memoized cell carries the abstract value.
\* Expected outcome: PASS.
\*
\* Cross-tree resolution: the canonical primitive module is resolved through
\* the verification runner's TLA module search path. No copy is vendored here.
\* ====================================================================
EXTENDS Naturals, FiniteSets

CONSTANTS
    k1, k2, k3, k4,   \* model values for the four keys
    NoKey,             \* model value: sentinel (not in Keys)
    BaseVal,           \* boundary value for keys with no predecessors
    StepVal            \* value added per predecessor in the recurrence

\* ── Value range (bounded for TLC) ────────────────────────────────────────────
\* With BaseVal=1, StepVal=1, max |Preds|=2: max value=3.  0..10 is ample.
ValRange == 0..10

\* ── Fixed topology ────────────────────────────────────────────────────────────
Keys   == {k1, k2, k3, k4}
DepRel == {<<k1, k2>>, <<k1, k3>>, <<k2, k4>>, <<k3, k4>>}

\* ── Topology helpers ──────────────────────────────────────────────────────────
Predecessors(k) == { p \in Keys : <<p, k>> \in DepRel }
Successors(k)   == { s \in Keys : <<k, s>> \in DepRel }

\* Abstract value: linear recurrence over predecessor count.
AbstractVal(k) == BaseVal + StepVal * Cardinality(Predecessors(k))

\* ── State variables ───────────────────────────────────────────────────────────
VARIABLES
    ab_filled,       \* abstract: set of keys whose abstract value is finalized
    memo,            \* ResourceRegistry component state: <<key, value>> pairs
    tq_queue,        \* connective (buffer): keys ready to be processed
    tq_visited,      \* connective (markers): keys already dequeued
    rd_key,          \* connective (marker): cell currently aggregating, or NoKey
    rd_remaining,    \* connective (buffer): predecessors not yet aggregated
    rd_accum         \* connective (accumulator): running partial

vars == <<ab_filled, memo, tq_queue, tq_visited, rd_key, rd_remaining, rd_accum>>

\* ── The composed primitive ───────────────────────────────────────────────────
\* The memo table is bound to the canonical registry's own variable, so the
\* component's operations and its obligation apply to it directly.
Registry == INSTANCE ResourceRegistry
              WITH Keys <- Keys, Values <- ValRange, entries <- memo

\* ── Memo helpers (projections over the component) ─────────────────────────────
IsMemoized(k) == \E v \in ValRange : <<k, v>> \in memo
MemoVal(k)    == CHOOSE v \in ValRange : <<k, v>> \in memo

AllPredsIn(k, tbl) ==
    \A p \in Predecessors(k) : \E v \in ValRange : <<p, v>> \in tbl

\* ── Type invariant ────────────────────────────────────────────────────────────
TypeInvariant ==
    /\ ab_filled    \subseteq Keys
    /\ Registry!TypeInvariant
    /\ tq_queue     \subseteq Keys
    /\ tq_visited   \subseteq Keys
    /\ rd_key       \in (Keys \cup {NoKey})
    /\ rd_remaining \subseteq Keys
    /\ rd_accum     \in ValRange

\* ── Init ──────────────────────────────────────────────────────────────────────
Init ==
    /\ ab_filled    = {}
    /\ Registry!Init
    /\ tq_queue     = { k \in Keys : Predecessors(k) = {} }   \* roots
    /\ tq_visited   = {}
    /\ rd_key       = NoKey
    /\ rd_remaining = {}
    /\ rd_accum     = 0

\* ── Abstract step: fill one ready key ─────────────────────────────────────────
AbsFill(k) ==
    /\ k \in Keys
    /\ k \notin ab_filled
    /\ \A p \in Predecessors(k) : p \in ab_filled
    /\ ab_filled' = ab_filled \cup {k}
    /\ UNCHANGED <<memo, tq_queue, tq_visited, rd_key, rd_remaining, rd_accum>>

\* ── Concrete step 1: take a ready key from the buffer ─────────────────────────
\* Inline: the canonical TraversalEngine hardcodes its topology and cannot be
\* bound to this DAG.
Dequeue(k) ==
    /\ rd_key = NoKey
    /\ k \in tq_queue
    /\ k \notin tq_visited
    /\ AllPredsIn(k, memo)
    /\ tq_visited'   = tq_visited \cup {k}
    /\ tq_queue'     = tq_queue   \ {k}
    /\ rd_key'       = k
    /\ rd_remaining' = Predecessors(k)
    /\ rd_accum'     = BaseVal
    /\ UNCHANGED <<ab_filled, memo>>

\* ── Concrete step 2: fold in one predecessor ──────────────────────────────────
\* Inline: canonical Reduction's Items set is a CONSTANT armed once by its
\* Init, so a per-cell fold cannot bind it.
Aggregate(p) ==
    /\ rd_key /= NoKey
    /\ p \in rd_remaining
    /\ rd_remaining' = rd_remaining \ {p}
    /\ rd_accum'     = rd_accum + StepVal
    /\ UNCHANGED <<ab_filled, memo, tq_queue, tq_visited, rd_key>>

\* ── Concrete step 3: the registry component commits the completed cell ────────
\* The upsert is Registry!Register; the newly-ready successors are then a
\* projection over the post-state table.
Commit ==
    /\ rd_key       /= NoKey
    /\ rd_remaining = {}
    /\ Registry!Register(rd_key, rd_accum)
    /\ tq_queue' = tq_queue \cup
           { s \in Successors(rd_key) :
               s \notin tq_visited /\
               s \notin tq_queue   /\
               AllPredsIn(s, memo') }
    /\ rd_key'       = NoKey
    /\ rd_remaining' = {}
    /\ rd_accum'     = 0
    /\ UNCHANGED <<ab_filled, tq_visited>>

\* ── Stutter when fully done ───────────────────────────────────────────────────
AllDone ==
    /\ ab_filled = Keys
    /\ \A k \in Keys : IsMemoized(k)
    /\ rd_key = NoKey

Stutter == AllDone /\ UNCHANGED vars

\* ── Next / Spec ───────────────────────────────────────────────────────────────
Next ==
    \/ \E k \in Keys : AbsFill(k)
    \/ \E k \in Keys : Dequeue(k)
    \/ \E p \in Keys : Aggregate(p)
    \/ Commit
    \/ Stutter

Spec == Init /\ [][Next]_vars

\* ── Refinement mapping ────────────────────────────────────────────────────────
\* Every memoized cell carries the abstract value.
RefinementHolds ==
    \A k \in Keys : IsMemoized(k) => MemoVal(k) = AbstractVal(k)

\* ── Additional safety invariants ──────────────────────────────────────────────

\* The component's own obligation, carried unchanged.
UniqueMapping == Registry!UniqueMapping

\* Abstract topological order.
AbstractTopoOrder ==
    \A k \in ab_filled :
        \A p \in Predecessors(k) : p \in ab_filled

\* Concrete topological order: visited keys had all preds memoized.
ConcreteTopoOrder ==
    \A k \in tq_visited :
        \A p \in Predecessors(k) : IsMemoized(p)

====
