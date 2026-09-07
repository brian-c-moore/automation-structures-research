---- MODULE ErlangBehavior ----
\* ====================================================================
\* ERLANG BEHAVIORAL SPEC (bounded study configuration)
\*
\* Behavioral property under the StreamGraph modality state machine
\* parameterized as Erlang (Pattern + Dynamic_Addressable +
\* Supervision_Tree): a message sent from actor A to actor B reaches
\* B's mailbox exactly once under normal operation.
\*
\* Conservation invariant `ExactlyOnceDelivery`:
\*   sends_a_to_b = Len(mailbox_b) + delivered_b
\*
\* every message A sent is either still inflight in B's mailbox or
\* has been delivered to B's process exactly once. Duplicate delivery
\* would push the right-hand side above the left; message loss would
\* push it below.
\* ====================================================================
EXTENDS Naturals, Sequences

CONSTANTS MaxSends, MaxMailbox

VARIABLES sends, mailbox, delivered

vars == <<sends, mailbox, delivered>>

TypeInvariant ==
    /\ sends     \in 0..MaxSends
    /\ mailbox   \in Seq(1..MaxSends)
    /\ delivered \in 0..MaxSends

Init ==
    /\ sends     = 0
    /\ mailbox   = <<>>
    /\ delivered = 0

\* A sends one message to B. Backpressure: B's mailbox must have room.
ASend ==
    /\ sends < MaxSends
    /\ Len(mailbox) < MaxMailbox
    /\ sends'   = sends + 1
    /\ mailbox' = Append(mailbox, sends + 1)
    /\ UNCHANGED delivered

\* B receives the head of its mailbox.
BReceive ==
    /\ Len(mailbox) > 0
    /\ mailbox'   = Tail(mailbox)
    /\ delivered' = delivered + 1
    /\ UNCHANGED sends

DoneStuttering ==
    /\ sends = MaxSends
    /\ Len(mailbox) = 0
    /\ UNCHANGED vars

Next == ASend \/ BReceive \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* ----- BEHAVIORAL INVARIANT -----
\* Conservation: every send is accounted for as either inflight or
\* delivered. No duplication, no loss. Holds trivially in this model
\* because ASend appends exactly one entry and BReceive removes
\* exactly one; the property is the formal witness that the model
\* preserves it.
ExactlyOnceDelivery == sends = Len(mailbox) + delivered
====
