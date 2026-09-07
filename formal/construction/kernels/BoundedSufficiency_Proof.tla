---- MODULE BoundedSufficiency_Proof ----
EXTENDS BoundedSufficiency, TLAPS

LEMMA InitInv == Init => Inv
BY DEF Init, Inv, TypeInvariant, AuthorizationObligation,
       EvidenceAttribution, CommitPhaseAgreement, ActiveAuthorization, Phases

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0, SMT DEF Inv, TypeInvariant, AuthorizationObligation,
                        EvidenceAttribution, CommitPhaseAgreement,
                        ActiveAuthorization, vars, Phases
  <1>A. CASE Admit
    BY <1>A, SMT DEF Inv, TypeInvariant, AuthorizationObligation,
                        EvidenceAttribution, CommitPhaseAgreement,
                        ActiveAuthorization, Admit, Phases
  <1>C. CASE GovernedCommit
    BY <1>C DEF Inv, TypeInvariant, AuthorizationObligation,
                 EvidenceAttribution, CommitPhaseAgreement,
                 ActiveAuthorization, GovernedCommit, Phases
  <1>D. CASE ClosedStuttering
    BY <1>D, SMT DEF Inv, TypeInvariant, AuthorizationObligation,
                        EvidenceAttribution, CommitPhaseAgreement,
                        ActiveAuthorization, ClosedStuttering, vars, Phases
  <1>N. CASE Next
    BY <1>N, <1>A, <1>C, <1>D DEF Next, ProgressStep
  <1> QED BY <1>0, <1>N

THEOREM Safety == Spec => []Inv
BY InitInv, NextInv, PTL DEF Spec

THEOREM AuthorizationSafety == Spec => []AuthorizationObligation
BY Safety, PTL DEF Inv

THEOREM EvidenceAttributionSafety == Spec => []EvidenceAttribution
BY Safety, PTL DEF Inv

LEMMA InvImpliesObservationAgreement == Inv => ObservationAgreement
BY SMT DEF Inv, CommitPhaseAgreement, ObservationAgreement,
           ConcreteObservation, AbstractObservation

THEOREM ObservationAgreementSafety == Spec => []ObservationAgreement
BY Safety, InvImpliesObservationAgreement, PTL

THEOREM AuthorizationGuaranteeDischargesEvidenceRely ==
    Inv /\ Admit => EvidenceAttribution'
BY DEF Inv, Admit, EvidenceAttribution

THEOREM SharedCommitPreservesBothObligations ==
    Inv /\ GovernedCommit
        => AuthorizationObligation' /\ EvidenceAttribution'
BY DEF Inv, GovernedCommit, AuthorizationObligation, EvidenceAttribution

LEMMA IdleLeadsToActive == Spec => (phase = "idle" ~> phase = "active")
  <1> DEFINE P == Inv /\ phase = "idle"
  <1> DEFINE Q == phase = "active"
  <1>1. P /\ [Next]_vars => P' \/ Q'
    BY NextInv DEF P, Q, Next, ProgressStep, Admit, GovernedCommit,
                       ClosedStuttering, vars
  <1>2. P /\ <<Next /\ ProgressStep>>_vars => Q'
    BY DEF P, Q, Next, ProgressStep, Admit, GovernedCommit, vars
  <1>3. P => ENABLED <<ProgressStep>>_vars
    BY ExpandENABLED DEF P, Inv, TypeInvariant,
                               AuthorizationObligation, EvidenceAttribution,
                               CommitPhaseAgreement, ActiveAuthorization,
                               ProgressStep, Admit, GovernedCommit, vars, Phases
  <1>wf. Spec => WF_vars(ProgressStep)
    BY DEF Spec, Fairness
  <1> QED
    BY <1>1, <1>2, <1>3, <1>wf, Safety, PTL DEF Spec, P, Q

LEMMA ActiveLeadsToClosed == Spec => (phase = "active" ~> phase = "closed")
  <1> DEFINE P == Inv /\ phase = "active"
  <1> DEFINE Q == phase = "closed"
  <1>1. P /\ [Next]_vars => P' \/ Q'
    BY NextInv DEF P, Q, Next, ProgressStep, Admit, GovernedCommit,
                       ClosedStuttering, vars
  <1>2. P /\ <<Next /\ ProgressStep>>_vars => Q'
    BY DEF P, Q, Next, ProgressStep, Admit, GovernedCommit, vars
  <1>3. P => ENABLED <<ProgressStep>>_vars
    BY ExpandENABLED DEF P, Inv, TypeInvariant,
                               AuthorizationObligation, EvidenceAttribution,
                               CommitPhaseAgreement, ActiveAuthorization,
                               ProgressStep, Admit, GovernedCommit, vars, Phases
  <1>wf. Spec => WF_vars(ProgressStep)
    BY DEF Spec, Fairness
  <1> QED
    BY <1>1, <1>2, <1>3, <1>wf, Safety, PTL DEF Spec, P, Q

THEOREM EventualClosureProved == Spec => EventualClosure
BY IdleLeadsToActive, ActiveLeadsToClosed, PTL
   DEF Spec, Init, EventualClosure, Closed

LEMMA InitRefines == Init => AbstractInit
BY DEF Init, AbstractInit

LEMMA NextRefines == Inv /\ [Next]_vars => [AbstractNext]_AbstractVars
BY SMT DEF Inv, Next, ProgressStep, Admit, GovernedCommit,
           ClosedStuttering, AbstractNext, AbstractAdmit,
           AbstractCommit, AbstractClosedStuttering,
           AbstractVars, vars

THEOREM RefinementProved == Spec => Refinement
  <1>1. Init => AbstractInit  BY InitRefines
  <1>2. Inv /\ [Next]_vars => [AbstractNext]_AbstractVars  BY NextRefines
  <1>3. Spec => []Inv  BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL
           DEF Spec, AbstractSpec, Refinement

THEOREM BoundedConstructionSufficiency ==
    Spec => RegisteredGuaranteeBundle
BY AuthorizationSafety, EvidenceAttributionSafety,
   EventualClosureProved, ObservationAgreementSafety, RefinementProved
   DEF RegisteredGuaranteeBundle

====
