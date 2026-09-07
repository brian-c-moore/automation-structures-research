---- MODULE RdpPremiseBinding ----
\* Safety model for the fixed-grid accounting premises used by
\* FEX-DOM-PRIV-01. Mironov's theorem remains the authority for the RDP
\* composition and conversion formula. This model treats the configured
\* penalty as a source premise and checks the executable projection, complete
\* minimum selection, hard capacity, identity, target, rejection, and order
\* relations around it.

EXTENDS Naturals, FiniteSets

CONSTANTS
    Accounts, ScopeA, ScopeB,
    Orders, LowOrder, HighOrder, OrderRank(_),
    Queries, QueryOne, QueryTwo, Cost(_, _), Penalty(_),
    Ceiling, NULL, Fault

Faults == {
    "None",
    "ReuseQueryIdentity",
    "OmitOrderCharge",
    "DropDeltaPenalty",
    "OmitBestCandidate",
    "ReverseSelection",
    "BypassCeiling",
    "MisdirectAccount",
    "MutateRejectedState",
    "SkipDecision"
}

ASSUME ModelTypes ==
    /\ Accounts = {ScopeA, ScopeB}
    /\ ScopeA # ScopeB
    /\ Orders = {LowOrder, HighOrder}
    /\ LowOrder # HighOrder
    /\ Queries = {QueryOne, QueryTwo}
    /\ QueryOne # QueryTwo
    /\ Ceiling \in Nat \ {0}
    /\ NULL \notin Accounts \cup Orders \cup Queries
    /\ \A order \in Orders :
        /\ OrderRank(order) \in Nat
        /\ Penalty(order) \in Nat
    /\ \A query \in Queries : \A order \in Orders : Cost(query, order) \in Nat
    /\ Fault \in Faults

VARIABLES
    phase, requestIndex, currentQuery, target, actualTarget,
    totals, reported, registry, releases,
    beforeTotals, beforeReported, beforeRegistry, beforeReleases,
    candidateTotals, candidates, suppliedOrders,
    winner, proposed, accepted,
    begun, selections, decisions, completed

vars == <<
    phase, requestIndex, currentQuery, target, actualTarget,
    totals, reported, registry, releases,
    beforeTotals, beforeReported, beforeRegistry, beforeReleases,
    candidateTotals, candidates, suppliedOrders,
    winner, proposed, accepted,
    begun, selections, decisions, completed
>>

ConfiguredOrderRank(order) == IF order = LowOrder THEN 1 ELSE 2
ConfiguredPenalty(order) == IF order = LowOrder THEN 4 ELSE 2
ConfiguredCost(query, order) ==
    IF query = QueryOne
    THEN IF order = LowOrder THEN 1 ELSE 2
    ELSE 10

EffectiveCost(query, order) ==
    IF Fault = "ReuseQueryIdentity" /\ requestIndex = 2 THEN 0
    ELSE Cost(query, order)

Bound(curve, order) == curve[order] + Penalty(order)

Precedes(left, right, values) ==
    \/ values[left] < values[right]
    \/ /\ values[left] = values[right]
       /\ OrderRank(left) <= OrderRank(right)

TypeInvariant ==
    /\ phase \in {"idle", "begun", "projected", "selected", "decided", "done"}
    /\ requestIndex \in 1..3
    /\ currentQuery \in Queries \cup {NULL}
    /\ target \in Accounts \cup {NULL}
    /\ actualTarget \in Accounts \cup {NULL}
    /\ totals \in [Accounts -> [Orders -> Nat]]
    /\ reported \in [Accounts -> Nat]
    /\ registry \in [Accounts -> SUBSET Queries]
    /\ releases \in [Accounts -> Nat]
    /\ beforeTotals \in [Accounts -> [Orders -> Nat]]
    /\ beforeReported \in [Accounts -> Nat]
    /\ beforeRegistry \in [Accounts -> SUBSET Queries]
    /\ beforeReleases \in [Accounts -> Nat]
    /\ candidateTotals \in [Orders -> Nat]
    /\ candidates \in [Orders -> Nat]
    /\ suppliedOrders \subseteq Orders
    /\ winner \in Orders \cup {NULL}
    /\ proposed \in Nat
    /\ accepted \in BOOLEAN
    /\ begun \in 0..2
    /\ selections \in 0..2
    /\ decisions \in 0..2
    /\ completed \in 0..2

ProjectionBinding ==
    phase \in {"projected", "selected", "decided"} =>
        \A order \in Orders : candidates[order] = Bound(candidateTotals, order)

CompleteCandidateSet ==
    phase \in {"projected", "selected", "decided"} => suppliedOrders = Orders

WinnerOptimality ==
    phase \in {"selected", "decided"} =>
        /\ winner \in suppliedOrders
        /\ proposed = candidates[winner]
        /\ \A order \in suppliedOrders : Precedes(winner, order, candidates)

CoordinateBinding ==
    phase = "decided" /\ accepted => totals[target] = candidateTotals

HardCapacity ==
    /\ \A account \in Accounts : reported[account] <= Ceiling
    /\ phase = "decided" /\ accepted => proposed <= Ceiling

QueryIdentityBinding ==
    phase = "decided" /\ accepted =>
        /\ currentQuery \notin beforeRegistry[target]
        /\ registry[target] = beforeRegistry[target] \cup {currentQuery}

TargetBinding ==
    phase = "decided" /\ accepted =>
        /\ actualTarget = target
        /\ \A account \in Accounts \ {target} :
            /\ totals[account] = beforeTotals[account]
            /\ reported[account] = beforeReported[account]
            /\ registry[account] = beforeRegistry[account]
            /\ releases[account] = beforeReleases[account]

RejectionNoninterference ==
    phase = "decided" /\ ~accepted =>
        /\ totals = beforeTotals
        /\ reported = beforeReported
        /\ registry = beforeRegistry
        /\ releases = beforeReleases

ReleaseBinding ==
    phase = "decided" =>
        IF accepted
        THEN releases[target] = beforeReleases[target] + 1
        ELSE releases = beforeReleases

SequentialOrder ==
    /\ completed <= decisions
    /\ decisions <= selections
    /\ selections <= begun
    /\ begun <= completed + 1

CompositionInvariant ==
    /\ ProjectionBinding
    /\ CompleteCandidateSet
    /\ WinnerOptimality
    /\ CoordinateBinding
    /\ HardCapacity
    /\ QueryIdentityBinding
    /\ TargetBinding
    /\ RejectionNoninterference
    /\ ReleaseBinding
    /\ SequentialOrder

ZeroCurve == [order \in Orders |-> 0]
ZeroTotals == [account \in Accounts |-> ZeroCurve]
EmptyRegistry == [account \in Accounts |-> {}]
ZeroAccounts == [account \in Accounts |-> 0]

Init ==
    /\ phase = "idle"
    /\ requestIndex = 1
    /\ currentQuery = NULL
    /\ target = NULL
    /\ actualTarget = NULL
    /\ totals = ZeroTotals
    /\ reported = ZeroAccounts
    /\ registry = EmptyRegistry
    /\ releases = ZeroAccounts
    /\ beforeTotals = ZeroTotals
    /\ beforeReported = ZeroAccounts
    /\ beforeRegistry = EmptyRegistry
    /\ beforeReleases = ZeroAccounts
    /\ candidateTotals = ZeroCurve
    /\ candidates = ZeroCurve
    /\ suppliedOrders = {}
    /\ winner = NULL
    /\ proposed = 0
    /\ accepted = FALSE
    /\ begun = 0
    /\ selections = 0
    /\ decisions = 0
    /\ completed = 0

Begin ==
    /\ phase = "idle"
    /\ requestIndex <= 2
    /\ currentQuery' =
        IF requestIndex = 1 \/ Fault = "ReuseQueryIdentity"
        THEN QueryOne
        ELSE QueryTwo
    /\ target' = ScopeA
    /\ actualTarget' = NULL
    /\ beforeTotals' = totals
    /\ beforeReported' = reported
    /\ beforeRegistry' = registry
    /\ beforeReleases' = releases
    /\ candidateTotals' = ZeroCurve
    /\ candidates' = ZeroCurve
    /\ suppliedOrders' = {}
    /\ winner' = NULL
    /\ proposed' = 0
    /\ accepted' = FALSE
    /\ begun' = begun + 1
    /\ phase' = "begun"
    /\ UNCHANGED <<
        requestIndex, totals, reported, registry, releases,
        selections, decisions, completed
        >>

Project ==
    /\ phase = "begun"
    /\ candidateTotals' =
        [order \in Orders |-> beforeTotals[target][order] + EffectiveCost(currentQuery, order)]
    /\ candidates' =
        [order \in Orders |->
            candidateTotals'[order] +
                IF Fault = "DropDeltaPenalty" THEN 0 ELSE Penalty(order)]
    /\ suppliedOrders' =
        IF Fault = "OmitBestCandidate" THEN Orders \ {HighOrder} ELSE Orders
    /\ phase' = "projected"
    /\ UNCHANGED <<
        requestIndex, currentQuery, target, actualTarget,
        totals, reported, registry, releases,
        beforeTotals, beforeReported, beforeRegistry, beforeReleases,
        winner, proposed, accepted,
        begun, selections, decisions, completed
        >>

Select(order) ==
    /\ phase = "projected"
    /\ order \in suppliedOrders
    /\ IF Fault = "ReverseSelection"
       THEN \A other \in suppliedOrders : Precedes(other, order, candidates)
       ELSE \A other \in suppliedOrders : Precedes(order, other, candidates)
    /\ winner' = order
    /\ proposed' = candidates[order]
    /\ selections' = selections + 1
    /\ phase' = "selected"
    /\ UNCHANGED <<
        requestIndex, currentQuery, target, actualTarget,
        totals, reported, registry, releases,
        beforeTotals, beforeReported, beforeRegistry, beforeReleases,
        candidateTotals, candidates, suppliedOrders, accepted,
        begun, decisions, completed
        >>

Decide ==
    /\ phase = "selected"
    /\ accepted' = (proposed <= Ceiling \/ Fault = "BypassCeiling")
    /\ actualTarget' =
        IF accepted'
        THEN IF Fault = "MisdirectAccount" THEN ScopeB ELSE target
        ELSE NULL
    /\ totals' =
        IF accepted'
        THEN [totals EXCEPT ![actualTarget'] =
            IF Fault = "OmitOrderCharge"
            THEN [candidateTotals EXCEPT ![LowOrder] = beforeTotals[target][LowOrder]]
            ELSE candidateTotals]
        ELSE IF Fault = "MutateRejectedState"
             THEN [totals EXCEPT ![target][LowOrder] = @ + 1]
             ELSE totals
    /\ reported' =
        IF accepted' THEN [reported EXCEPT ![actualTarget'] = proposed] ELSE reported
    /\ registry' =
        IF accepted'
        THEN [registry EXCEPT ![actualTarget'] = @ \cup {currentQuery}]
        ELSE registry
    /\ releases' =
        IF accepted' THEN [releases EXCEPT ![actualTarget'] = @ + 1] ELSE releases
    /\ decisions' = decisions + 1
    /\ phase' = "decided"
    /\ UNCHANGED <<
        requestIndex, currentQuery, target,
        beforeTotals, beforeReported, beforeRegistry, beforeReleases,
        candidateTotals, candidates, suppliedOrders, winner, proposed,
        begun, selections, completed
        >>

Complete ==
    /\ \/ phase = "decided"
       \/ /\ Fault = "SkipDecision"
          /\ phase = "selected"
    /\ requestIndex' = requestIndex + 1
    /\ completed' = completed + 1
    /\ phase' = "idle"
    /\ UNCHANGED <<
        currentQuery, target, actualTarget,
        totals, reported, registry, releases,
        beforeTotals, beforeReported, beforeRegistry, beforeReleases,
        candidateTotals, candidates, suppliedOrders,
        winner, proposed, accepted,
        begun, selections, decisions
        >>

Finish ==
    /\ phase = "idle"
    /\ requestIndex = 3
    /\ phase' = "done"
    /\ UNCHANGED <<
        requestIndex, currentQuery, target, actualTarget,
        totals, reported, registry, releases,
        beforeTotals, beforeReported, beforeRegistry, beforeReleases,
        candidateTotals, candidates, suppliedOrders,
        winner, proposed, accepted,
        begun, selections, decisions, completed
        >>

Next ==
    \/ Begin
    \/ Project
    \/ \E order \in Orders : Select(order)
    \/ Decide
    \/ Complete
    \/ Finish

Spec == Init /\ [][Next]_vars

====
