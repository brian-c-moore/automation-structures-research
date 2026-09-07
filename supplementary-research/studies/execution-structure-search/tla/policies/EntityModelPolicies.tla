---- MODULE EntityModelPolicies ----
\* ============================================================
\* POLICY SPEC: ENTITY MODEL (docs/execution-modalities.md)
\*
\* Four entity values: how work is attached and addressed.
\* This spec models a tiny system in which `bind` and `emit_to`
\* events occur, and verifies that under each EntityModel value
\* the events respect the addressing discipline declared.
\* ============================================================
EXTENDS Naturals, FiniteSets

CONSTANTS Workers, Slots, Mode, MaxEvents

ASSUME Mode \in {"anonymous", "named", "addressable", "channel"}

\* For anonymous and named, work is bound to slots/nodes at init.
\* For addressable, refs are learned at runtime.
\* For channel, channel endpoints are first-class.

VARIABLES bindings, refs, channels, events

vars == <<bindings, refs, channels, events>>

TypeInvariant ==
    /\ bindings \in [Slots -> Workers \cup {"unbound"}]
    /\ refs     \in [Workers -> SUBSET Workers]
    /\ channels \subseteq Workers \X Workers
    /\ events   \in 0..MaxEvents

Init ==
    /\ bindings = [s \in Slots |->
                     IF Mode \in {"anonymous", "named"}
                     THEN CHOOSE w \in Workers : TRUE
                     ELSE "unbound"]
    /\ refs     = [w \in Workers |-> {}]
    /\ channels = {}
    /\ events   = 0

\* anonymous: work attaches to positional slots only. No refs, no channels.
EmitAnonymous(s) ==
    /\ Mode = "anonymous"
    /\ events < MaxEvents
    /\ bindings[s] # "unbound"
    /\ events' = events + 1
    /\ UNCHANGED <<bindings, refs, channels>>

\* named: same as anonymous but slot names are observable. Modeled
\* identically; the test of named vs anonymous lives in workloads.
EmitNamed(s) ==
    /\ Mode = "named"
    /\ events < MaxEvents
    /\ bindings[s] # "unbound"
    /\ events' = events + 1
    /\ UNCHANGED <<bindings, refs, channels>>

\* addressable: workers learn refs to each other at runtime; sends are
\* along refs.
LearnRef(a, b) ==
    /\ Mode = "addressable"
    /\ a # b
    /\ b \notin refs[a]
    /\ events < MaxEvents
    /\ refs' = [refs EXCEPT ![a] = refs[a] \cup {b}]
    /\ events' = events + 1
    /\ UNCHANGED <<bindings, channels>>

SendAddressable(a, b) ==
    /\ Mode = "addressable"
    /\ b \in refs[a]
    /\ events < MaxEvents
    /\ events' = events + 1
    /\ UNCHANGED <<bindings, refs, channels>>

\* channel: an endpoint pair is created; sends go on channels.
OpenChannel(a, b) ==
    /\ Mode = "channel"
    /\ a # b
    /\ <<a, b>> \notin channels
    /\ events < MaxEvents
    /\ channels' = channels \cup {<<a, b>>}
    /\ events' = events + 1
    /\ UNCHANGED <<bindings, refs>>

SendOnChannel(a, b) ==
    /\ Mode = "channel"
    /\ <<a, b>> \in channels
    /\ events < MaxEvents
    /\ events' = events + 1
    /\ UNCHANGED <<bindings, refs, channels>>

Done ==
    /\ events = MaxEvents
    /\ UNCHANGED vars

Next ==
    \/ \E s \in Slots : EmitAnonymous(s) \/ EmitNamed(s)
    \/ \E a, b \in Workers :
         LearnRef(a, b) \/ SendAddressable(a, b)
         \/ OpenChannel(a, b) \/ SendOnChannel(a, b)
    \/ Done

Spec == Init /\ [][Next]_vars

\* ----- INVARIANTS -----

\* Anonymous: refs and channels are empty at all times.
AnonymousNoRefs ==
    Mode = "anonymous" => refs = [w \in Workers |-> {}] /\ channels = {}

\* Named: same as anonymous structurally (names observed at the
\* runtime/TOML level, not modeled here).
NamedNoRefs ==
    Mode = "named" => refs = [w \in Workers |-> {}] /\ channels = {}

\* Addressable: no channels appear; every send is along a known ref.
\* The latter is structural — guarded by SendAddressable's precondition.
AddressableNoChannels ==
    Mode = "addressable" => channels = {}

\* Channel: refs are not used.
ChannelNoRefs ==
    Mode = "channel" => refs = [w \in Workers |-> {}]
====
