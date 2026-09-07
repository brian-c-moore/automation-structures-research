--------------------- MODULE GovernedCommitBridge_Proof ---------------------
EXTENDS GovernedCommitExecutable, TLAPS

LEMMA BasicTypeInitialization == Init => BasicTypeInvariant
  <1> SUFFICES ASSUME Init PROVE BasicTypeInvariant OBVIOUS
  <1>1. phase \in ConcretePhases /\ registryMapped \in BOOLEAN
         /\ actuationEffect \in BOOLEAN /\ effectApplied \in BOOLEAN
         /\ evidencePersisted \in BOOLEAN /\ recoveryIntent \in BOOLEAN
         /\ crashed \in BOOLEAN /\ lastClass \in ActionClasses
    BY DEF Init, ConcretePhases, ActionClasses
  <1>2. capacity \in Nat /\ reserved \in Nat /\ allocated \in Nat
         /\ reserved + allocated <= capacity
         /\ propagationIteration \in Nat /\ propagationIteration <= 1
         /\ auditLen \in Nat /\ auditLen <= 1 /\ pc \in Nat /\ pc <= 3
         /\ attempts \in Nat /\ maxAttempts \in Nat /\ maxAttempts > 0
         /\ attempts <= maxAttempts
    BY SMT DEF Init
  <1> QED BY <1>1, <1>2 DEF BasicTypeInvariant

LEMMA RepresentationInitialization == Init => RepresentationCoupling
BY DEF Init, RepresentationCoupling

LEMMA PhaseInitialization == Init => PhaseCoupling
BY DEF Init, PhaseCoupling

THEOREM TypeInitialization == Init => TypeInvariant
BY BasicTypeInitialization, RepresentationInitialization, PhaseInitialization
   DEF TypeInvariant

THEOREM InitializationRefinement == Init => AbstractInit(AbsState)
  <1> SUFFICES ASSUME Init PROVE AbstractInit(AbsState) OBVIOUS
  <1>1. AbsState.phase \in AbstractPhases
    BY DEF Init, AbsState, AbsPhase, AbstractPhases
  <1>2. AbsState.capacity \in Nat /\ AbsState.used \in Nat
         /\ AbsState.used <= AbsState.capacity
    BY SMT DEF Init, AbsState
  <1>3. AbsState.effect \in BOOLEAN /\ AbsState.audited \in BOOLEAN
         /\ AbsState.recovery \in BOOLEAN /\ AbsState.lastClass \in ActionClasses
    BY DEF Init, AbsState, ActionClasses
  <1>4. AbstractType(AbsState)
    BY <1>1, <1>2, <1>3 DEF AbstractType
  <1>5. AbsState.phase = "pending" /\ AbsState.used = 0
         /\ ~AbsState.effect /\ ~AbsState.audited /\ ~AbsState.recovery
         /\ AbsState.lastClass = "init"
    BY DEF Init, AbsState, AbsPhase
  <1> QED BY <1>4, <1>5 DEF AbstractInit

THEOREM AdmitAcceptedRefinement ==
    TypeInvariant /\ AdmitAccepted => AbstractSystemStep(AbsState, AbsState')
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
       PhaseCoupling, AdmitAccepted, AbstractSystemStep,
       AbsState, AbsPhase

THEOREM AdmitRejectedRefinement ==
    TypeInvariant /\ AdmitRejected => AbstractFailureStep(AbsState, AbsState')
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
       PhaseCoupling, AdmitRejected, AbstractFailureStep,
       AbsState, AbsPhase

THEOREM PropagateRefinement ==
    TypeInvariant /\ Propagate => AbstractSystemStep(AbsState, AbsState')
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
       PhaseCoupling, Propagate, AbstractSystemStep,
       AbsState, AbsPhase

THEOREM FailBeforeEffectRefinement ==
    TypeInvariant /\ FailBeforeEffect => AbstractFailureStep(AbsState, AbsState')
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
       PhaseCoupling, FailBeforeEffect, AbstractFailureStep,
       AbsState, AbsPhase

THEOREM FailAfterEffectRefinement ==
    TypeInvariant /\ FailAfterEffect => AbstractFailureStep(AbsState, AbsState')
BY DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
       PhaseCoupling, FailAfterEffect, AbstractFailureStep,
       AbsState, AbsPhase

THEOREM CommitSuccessRefinement ==
    TypeInvariant /\ CommitSuccess => AbstractCommitStep(AbsState, AbsState')
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
       PhaseCoupling, CommitSuccess, AbstractCommitStep,
       AbsState, AbsPhase

THEOREM RecoverRefinement ==
    TypeInvariant /\ Recover => AbstractCommitStep(AbsState, AbsState')
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
       PhaseCoupling, Recover, AbstractCommitStep,
       AbsState, AbsPhase

THEOREM CrashRefinement ==
    TypeInvariant /\ Crash => AbstractFailureStep(AbsState, AbsState')
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
       PhaseCoupling, Crash, AbstractFailureStep,
       AbsState, AbsPhase

THEOREM RestartRefinement ==
    TypeInvariant /\ Restart => AbstractStutterStep(AbsState, AbsState')
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
       PhaseCoupling, Restart, AbstractStutterStep,
       AbsState, AbsPhase

THEOREM EveryExecutableStepRefines ==
    TypeInvariant /\ Next => AbstractStep(AbsState, AbsState')
BY AdmitAcceptedRefinement, AdmitRejectedRefinement, PropagateRefinement,
   FailBeforeEffectRefinement, FailAfterEffectRefinement,
   CommitSuccessRefinement, RecoverRefinement, CrashRefinement,
   RestartRefinement
   DEF Next, AbstractStep

THEOREM ExactCommitPreimage ==
    Next => (CommitActions <=> AbsState'.lastClass = "commit")
BY SMT DEF Next, CommitActions, AdmitAccepted, AdmitRejected, Propagate,
       FailBeforeEffect, FailAfterEffect, CommitSuccess, Recover, Crash,
       Restart, AbsState

THEOREM ExactFailurePreimage ==
    Next => (FailureActions <=> AbsState'.lastClass = "failure")
BY SMT DEF Next, FailureActions, AdmitAccepted, AdmitRejected, Propagate,
       FailBeforeEffect, FailAfterEffect, CommitSuccess, Recover, Crash,
       Restart, AbsState

THEOREM ObservationAgreement ==
    TypeInvariant => ConcreteObservation = AbstractObservation(AbsState)
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
           PhaseCoupling, ConcretePhases, ConcreteObservation,
           AbstractObservation, AbsState, AbsPhase

THEOREM CrashPreservesDurableCommitEvidence ==
    TypeInvariant /\ phase = "Committed" /\ Crash
      => phase' = "Committed" /\ effectApplied' /\ evidencePersisted'
BY SMT DEF TypeInvariant, PhaseCoupling, Crash

THEOREM PartialFailurePreservesRecoveryIntent ==
    TypeInvariant /\ FailAfterEffect
      => phase' = "RecoveryPending" /\ effectApplied' /\ recoveryIntent'
         /\ ~evidencePersisted'
BY SMT DEF TypeInvariant, FailAfterEffect

THEOREM CommitAtomicityAndEvidence ==
    TypeInvariant /\ CommitActions
      => allocated' = 1 /\ reserved' = 0 /\ effectApplied'
         /\ evidencePersisted' /\ phase' = "Committed"
  <1>1. TypeInvariant /\ CommitSuccess
         => allocated' = 1 /\ reserved' = 0 /\ effectApplied'
            /\ evidencePersisted' /\ phase' = "Committed"
    BY DEF CommitSuccess
  <1>2. TypeInvariant /\ Recover
         => allocated' = 1 /\ reserved' = 0 /\ effectApplied'
            /\ evidencePersisted' /\ phase' = "Committed"
    BY DEF TypeInvariant, PhaseCoupling, Recover
  <1> QED BY <1>1, <1>2 DEF CommitActions

THEOREM AdmitAcceptedTypePreservation ==
    TypeInvariant /\ AdmitAccepted => TypeInvariant'
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
           PhaseCoupling, AdmitAccepted, ConcretePhases, ActionClasses

THEOREM AdmitRejectedTypePreservation ==
    TypeInvariant /\ AdmitRejected => TypeInvariant'
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
           PhaseCoupling, AdmitRejected, ConcretePhases, ActionClasses

THEOREM PropagateTypePreservation ==
    TypeInvariant /\ Propagate => TypeInvariant'
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
           PhaseCoupling, Propagate, ConcretePhases, ActionClasses

THEOREM FailBeforeEffectTypePreservation ==
    TypeInvariant /\ FailBeforeEffect => TypeInvariant'
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
           PhaseCoupling, FailBeforeEffect, ConcretePhases, ActionClasses

THEOREM FailAfterEffectTypePreservation ==
    TypeInvariant /\ FailAfterEffect => TypeInvariant'
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
           PhaseCoupling, FailAfterEffect, ConcretePhases, ActionClasses

LEMMA CommitSuccessBasicTypePreservation ==
    TypeInvariant /\ CommitSuccess => BasicTypeInvariant'
  <1> SUFFICES ASSUME TypeInvariant, CommitSuccess
       PROVE BasicTypeInvariant' OBVIOUS
  <1>1. capacity \in Nat /\ reserved \in Nat /\ allocated \in Nat
         /\ reserved + allocated <= capacity /\ propagationIteration \in Nat
         /\ propagationIteration <= 1 /\ attempts \in Nat
         /\ maxAttempts \in Nat /\ maxAttempts > 0
    BY DEF TypeInvariant, BasicTypeInvariant
  <1>2. phase' \in ConcretePhases /\ capacity' \in Nat
         /\ reserved' \in Nat /\ allocated' \in Nat
         /\ reserved' + allocated' <= capacity'
         /\ propagationIteration' \in Nat /\ propagationIteration' <= 1
         /\ auditLen' \in Nat /\ auditLen' <= 1 /\ pc' \in Nat /\ pc' <= 3
         /\ attempts' \in Nat /\ maxAttempts' \in Nat /\ maxAttempts' > 0
         /\ attempts' <= maxAttempts'
    <2> USE <1>1
    <2> QED BY SMT DEF CommitSuccess, ConcretePhases
  <1>3. registryMapped' \in BOOLEAN /\ actuationEffect' \in BOOLEAN
         /\ effectApplied' \in BOOLEAN /\ evidencePersisted' \in BOOLEAN
         /\ recoveryIntent' \in BOOLEAN /\ crashed' \in BOOLEAN
         /\ lastClass' \in ActionClasses
    BY DEF TypeInvariant, BasicTypeInvariant, CommitSuccess, ActionClasses
  <1> QED BY <1>2, <1>3 DEF BasicTypeInvariant

LEMMA CommitSuccessRepresentationPreservation ==
    TypeInvariant /\ CommitSuccess => RepresentationCoupling'
BY DEF TypeInvariant, RepresentationCoupling, CommitSuccess

LEMMA CommitSuccessPhasePreservation ==
    TypeInvariant /\ CommitSuccess => PhaseCoupling'
BY DEF TypeInvariant, PhaseCoupling, CommitSuccess

THEOREM CommitSuccessTypePreservation ==
    TypeInvariant /\ CommitSuccess => TypeInvariant'
BY CommitSuccessBasicTypePreservation,
   CommitSuccessRepresentationPreservation, CommitSuccessPhasePreservation
   DEF TypeInvariant

LEMMA RecoverBasicTypePreservation ==
    TypeInvariant /\ Recover => BasicTypeInvariant'
  <1> SUFFICES ASSUME TypeInvariant, Recover PROVE BasicTypeInvariant' OBVIOUS
  <1>1. capacity \in Nat /\ reserved \in Nat /\ allocated \in Nat
         /\ reserved + allocated <= capacity /\ propagationIteration \in Nat
         /\ propagationIteration <= 1 /\ attempts \in Nat
         /\ maxAttempts \in Nat /\ maxAttempts > 0 /\ attempts <= maxAttempts
    BY DEF TypeInvariant, BasicTypeInvariant
  <1>2. phase' \in ConcretePhases /\ capacity' \in Nat
         /\ reserved' \in Nat /\ allocated' \in Nat
         /\ reserved' + allocated' <= capacity'
         /\ propagationIteration' \in Nat /\ propagationIteration' <= 1
         /\ auditLen' \in Nat /\ auditLen' <= 1 /\ pc' \in Nat /\ pc' <= 3
         /\ attempts' \in Nat /\ maxAttempts' \in Nat /\ maxAttempts' > 0
         /\ attempts' <= maxAttempts'
    <2> USE <1>1
    <2> QED BY SMT DEF Recover, ConcretePhases
  <1>3. registryMapped' \in BOOLEAN /\ actuationEffect' \in BOOLEAN
         /\ effectApplied' \in BOOLEAN /\ evidencePersisted' \in BOOLEAN
         /\ recoveryIntent' \in BOOLEAN /\ crashed' \in BOOLEAN
         /\ lastClass' \in ActionClasses
    BY DEF TypeInvariant, BasicTypeInvariant, Recover, ActionClasses
  <1> QED BY <1>2, <1>3 DEF BasicTypeInvariant

LEMMA RecoverRepresentationPreservation ==
    TypeInvariant /\ Recover => RepresentationCoupling'
BY DEF TypeInvariant, RepresentationCoupling, PhaseCoupling, Recover

LEMMA RecoverPhasePreservation ==
    TypeInvariant /\ Recover => PhaseCoupling'
BY DEF TypeInvariant, PhaseCoupling, Recover

THEOREM RecoverTypePreservation ==
    TypeInvariant /\ Recover => TypeInvariant'
BY RecoverBasicTypePreservation, RecoverRepresentationPreservation,
   RecoverPhasePreservation DEF TypeInvariant

THEOREM CrashTypePreservation == TypeInvariant /\ Crash => TypeInvariant'
BY SMT DEF TypeInvariant, BasicTypeInvariant, RepresentationCoupling,
           PhaseCoupling, Crash, ConcretePhases, ActionClasses

LEMMA RestartBasicTypePreservation ==
    TypeInvariant /\ Restart => BasicTypeInvariant'
BY DEF TypeInvariant, BasicTypeInvariant, Restart, ActionClasses

LEMMA RestartRepresentationPreservation ==
    TypeInvariant /\ Restart => RepresentationCoupling'
BY DEF TypeInvariant, RepresentationCoupling, Restart

LEMMA RestartPhasePreservation ==
    TypeInvariant /\ Restart => PhaseCoupling'
BY DEF TypeInvariant, PhaseCoupling, Restart

THEOREM RestartTypePreservation == TypeInvariant /\ Restart => TypeInvariant'
BY RestartBasicTypePreservation, RestartRepresentationPreservation,
   RestartPhasePreservation DEF TypeInvariant

THEOREM TypePreservation == TypeInvariant /\ Next => TypeInvariant'
BY AdmitAcceptedTypePreservation, AdmitRejectedTypePreservation,
   PropagateTypePreservation, FailBeforeEffectTypePreservation,
   FailAfterEffectTypePreservation, CommitSuccessTypePreservation,
   RecoverTypePreservation, CrashTypePreservation, RestartTypePreservation
   DEF Next

THEOREM AttemptArithmeticBounded ==
    TypeInvariant /\ Next => attempts' <= maxAttempts'
BY TypePreservation DEF TypeInvariant, BasicTypeInvariant

THEOREM GuaranteeInitialization == Init => TransferredGuarantee
BY SMT DEF Init, TransferredGuarantee, CapacitySafe, CommitEvidenceCoupled

THEOREM GuaranteePreservation ==
    TypeInvariant /\ TransferredGuarantee /\ Next => TransferredGuarantee'
BY TypePreservation DEF TypeInvariant, BasicTypeInvariant, PhaseCoupling,
                        TransferredGuarantee, CapacitySafe,
                        CommitEvidenceCoupled

THEOREM SchedulerActionsPreserveRefinement ==
    TypeInvariant /\ (AdmitAccepted \/ AdmitRejected \/ Propagate \/
                      CommitSuccess \/ Recover \/ Restart)
      => AbstractStep(AbsState, AbsState')
BY EveryExecutableStepRefines DEF Next

=============================================================================
