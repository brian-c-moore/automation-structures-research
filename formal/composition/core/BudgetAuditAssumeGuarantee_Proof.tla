---- MODULE BudgetAuditAssumeGuarantee_Proof ----
\* Discharges the generic assume-guarantee premises for the concrete
\* fault-free Budget/audit state and step relations.

EXTENDS BudgetAuditAssumeGuarantee, TLAPS

AGProof == INSTANCE AssumeGuaranteeRule_Proof
        WITH S <- States,
             InvA <- BudgetStates,
             InvB <- AuditStates,
             StepA <- BudgetStep,
             StepB <- AuditStep,
             RelyA <- BudgetRely,
             RelyB <- AuditRely

LEMMA WellTypedProof == AGProof!WellTyped
  BY SMT DEF AGProof!WellTyped, AGProof!Pairs, States, BudgetStates, AuditStates,
             BudgetStep, AuditStep, BudgetRely, AuditRely,
             ReserveRel, RejectRel, CommitRel, TerminalRel, Pairs

LEMMA BudgetStableProof ==
    AGProof!Stable(BudgetStates, BudgetStep \cup BudgetRely)
  BY SMT DEF AGProof!Stable, BudgetStates, BudgetStep, BudgetRely, AuditStep,
             ReserveRel, RejectRel, CommitRel, TerminalRel, States, Pairs

LEMMA AuditStableProof ==
    AGProof!Stable(AuditStates, AuditStep \cup AuditRely)
  BY SMT DEF AGProof!Stable, AuditStates, AuditStep, AuditRely, BudgetStep,
             ReserveRel, RejectRel, CommitRel, TerminalRel, States, Pairs

LEMMA RelyDischargeProof ==
    /\ BudgetStep \subseteq AuditRely
    /\ AuditStep \subseteq BudgetRely
  BY DEF BudgetRely, AuditRely

THEOREM ConcreteContract == AGProof!Contract
  BY WellTypedProof, BudgetStableProof, AuditStableProof, RelyDischargeProof
     DEF AGProof!Contract

THEOREM ActionPartition == ConcreteNoFaultStep = ComposedStepRel
  BY SMT DEF ConcreteNoFaultStep, ComposedStepRel, BudgetStep, AuditStep,
             ReserveRel, RejectRel, CommitRel, TerminalRel

THEOREM ConcreteCompositionStable ==
    AGProof!Stable(ComposedInvariantStates, ConcreteNoFaultStep)
  <1>1. AGProof!Stable(AGProof!ComposedInvariant, AGProof!ComposedStep)
    BY ConcreteContract, AGProof!AssumeGuaranteeComposition
  <1>2. AGProof!ComposedInvariant = ComposedInvariantStates
    BY DEF AGProof!ComposedInvariant, ComposedInvariantStates
  <1>3. AGProof!ComposedStep = ConcreteNoFaultStep
    BY ActionPartition DEF AGProof!ComposedStep, ComposedStepRel
  <1> QED  BY <1>1, <1>2, <1>3
====
