---- MODULE ALKClaimInstantiation_Proof ----
EXTENDS ALKClaimInstantiationWitness, TLAPS

ProductInvariant == BudgetContract!Inv /\ SequentialContract!Inv

LEMMA InitProductInvariant == Init => ProductInvariant
  <1> SUFFICES ASSUME Init PROVE ProductInvariant  OBVIOUS
  <1>1. BudgetContract!Inv
    BY BudgetContract!InitInv DEF Init
  <1>2. SequentialContract!Inv
    BY SequentialContract!InitInv DEF Init
  <1> QED  BY <1>1, <1>2 DEF ProductInvariant

LEMMA NextProductInvariant ==
    ProductInvariant /\ [Next]_vars => ProductInvariant'
  <1> SUFFICES ASSUME ProductInvariant, [Next]_vars
               PROVE ProductInvariant'  OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY SMT, <1>0
       DEF vars, ProductInvariant,
           BudgetContract!Inv, BudgetContract!TypeInvariant,
           BudgetContract!SafetyInvariant,
           SequentialContract!Inv, SequentialContract!TypeInvariant,
           SequentialContract!HistoryPositionAgreement,
           SequentialContract!ActiveBeforeDone
  <1>A. CASE BudgetStep
    <2>1. BudgetContract!Inv /\
           [BudgetContract!Next]_BudgetContract!vars
      BY <1>A DEF BudgetStep, ProductInvariant
    <2>2. BudgetContract!Inv'
      BY <2>1, BudgetContract!NextInv
    <2>3. SequentialContract!Inv'
      BY SMT, <1>A
         DEF BudgetStep, sequentialVars, SequentialContract!vars,
             ProductInvariant, SequentialContract!Inv,
             SequentialContract!TypeInvariant,
             SequentialContract!HistoryPositionAgreement,
             SequentialContract!ActiveBeforeDone
    <2> QED  BY <2>2, <2>3 DEF ProductInvariant
  <1>B. CASE SequentialStep
    <2>1. BudgetContract!Inv'
      BY SMT, <1>B
         DEF SequentialStep, budgetVars, BudgetContract!vars,
             ProductInvariant, BudgetContract!Inv,
             BudgetContract!TypeInvariant,
             BudgetContract!SafetyInvariant
    <2>2. SequentialContract!Inv /\
           [SequentialContract!Next]_SequentialContract!vars
      BY <1>B DEF SequentialStep, ProductInvariant
    <2>3. SequentialContract!Inv'
      BY <2>2, SequentialContract!NextInv
    <2> QED  BY <2>1, <2>3 DEF ProductInvariant
  <1>C. CASE Next
    BY <1>C, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>C

THEOREM ProductSafety == Spec => []ProductInvariant
  <1>1. Init => ProductInvariant  BY InitProductInvariant
  <1>2. ProductInvariant /\ [Next]_vars => ProductInvariant'
    BY NextProductInvariant
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA ProductInvariantImpliesSelectedPredicates ==
    ProductInvariant => SelectedPredicatesHold
BY DEF ProductInvariant, SelectedPredicatesHold,
       BudgetContract!Inv, SequentialContract!Inv

THEOREM SelectedCatalogPredicatesSafety ==
    Spec => []SelectedPredicatesHold
BY ProductSafety, ProductInvariantImpliesSelectedPredicates, PTL

LEMMA SelectedPredicatesImplyClauseBinding ==
    SelectedPredicatesHold => SelectedSchemaClauseBindingHeld
  <1> SUFFICES ASSUME SelectedPredicatesHold
               PROVE SelectedSchemaClauseBindingHeld  OBVIOUS
  <1>registry. /\ RegistrySchemaClauses["AS-BUD-CAP"] =
                     {"Budget!SafetyInvariant"}
                /\ RegistrySchemaClauses["EX-SEQ-SERIAL"] =
                     {"Sequential!TypeInvariant",
                      "Sequential!HistoryPositionAgreement"}
                /\ RegistryClauseStatusOf["Budget!SafetyInvariant"] = "primary"
                /\ RegistryClauseStatusOf["Sequential!TypeInvariant"] = "support"
                /\ RegistryClauseStatusOf[
                     "Sequential!HistoryPositionAgreement"] = "contributing"
                /\ SelectedSchemas = {"AS-BUD-CAP", "EX-SEQ-SERIAL"}
                /\ SelectedClauseOccurrences =
                     {"Budget!SafetyInvariant", "Sequential!TypeInvariant",
                      "Sequential!HistoryPositionAgreement"}
    <2>budgetClauses. RegistrySchemaClauses["AS-BUD-CAP"] =
                         {"Budget!SafetyInvariant"}
      BY Zenon DEF RegistrySchemaClauses, RegistryObligationSchemaNames
    <2>sequentialClauses. RegistrySchemaClauses["EX-SEQ-SERIAL"] =
                             {"Sequential!TypeInvariant",
                              "Sequential!HistoryPositionAgreement"}
      BY Zenon DEF RegistrySchemaClauses, RegistryObligationSchemaNames
    <2>budgetRole. RegistryClauseStatusOf["Budget!SafetyInvariant"] = "primary"
      BY Zenon DEF RegistryClauseStatusOf, RegistryClauseOccurrenceNames
    <2>typingRole. RegistryClauseStatusOf["Sequential!TypeInvariant"] = "support"
      BY Zenon DEF RegistryClauseStatusOf, RegistryClauseOccurrenceNames
    <2>historyRole. RegistryClauseStatusOf[
                       "Sequential!HistoryPositionAgreement"] = "contributing"
      BY Zenon DEF RegistryClauseStatusOf, RegistryClauseOccurrenceNames
    <2>schemas. SelectedSchemas = {"AS-BUD-CAP", "EX-SEQ-SERIAL"}
      BY Zenon DEF SelectedSchemas, SelectedStructureSchemas,
                   SelectedExecutionSchemas
    <2>occurrences. SelectedClauseOccurrences =
                        {"Budget!SafetyInvariant", "Sequential!TypeInvariant",
                         "Sequential!HistoryPositionAgreement"}
      BY Zenon, <2>budgetClauses, <2>sequentialClauses
         DEF SelectedClauseOccurrences, SelectedStructureClauseOccurrences,
             SelectedExecutionClauseOccurrences, SelectedStructureSchemas,
             SelectedExecutionSchemas
    <2> QED
      BY <2>budgetClauses, <2>sequentialClauses, <2>budgetRole,
         <2>typingRole, <2>historyRole, <2>schemas, <2>occurrences
  <1>budget. SelectedPredicateHolds["Budget!SafetyInvariant"]
    BY Zenon, <1>registry
       DEF SelectedPredicatesHold, SelectedPredicateHolds
  <1>typing. SelectedPredicateHolds["Sequential!TypeInvariant"]
    BY Zenon, <1>registry
       DEF SelectedPredicatesHold, SelectedPredicateHolds
  <1>history. SelectedPredicateHolds["Sequential!HistoryPositionAgreement"]
    BY Zenon, <1>registry
       DEF SelectedPredicatesHold, SelectedPredicateHolds
  <1>meaning. /\ SelectedClauseMeaning["Budget!SafetyInvariant"] = {TRUE}
               /\ SelectedClauseMeaning["Sequential!TypeInvariant"] = {TRUE}
               /\ SelectedClauseMeaning[
                    "Sequential!HistoryPositionAgreement"] = {TRUE}
    BY Zenon, <1>registry, <1>budget, <1>typing, <1>history
       DEF SelectedClauseMeaning
  <1>responsibility. /\ SelectedResponsibilityHolds["AS-BUD-CAP"]
                      /\ SelectedResponsibilityHolds["EX-SEQ-SERIAL"]
    BY Zenon, <1>registry
       DEF SelectedResponsibilityHolds, SelectedPredicatesHold
  <1>budgetBinding.
      SemanticClauseBinding(
          "state-safety", {TRUE}, RegistrySchemaClauses["AS-BUD-CAP"],
          SelectedClauseRoles("AS-BUD-CAP"),
          [clause \in RegistrySchemaClauses["AS-BUD-CAP"] |->
              SelectedClauseMeaning[clause]],
          IF SelectedResponsibilityHolds["AS-BUD-CAP"] THEN {TRUE} ELSE {},
          {TRUE}, [clause \in {} |-> {}], [clause \in {} |-> {}])
    BY Zenon, <1>registry, <1>meaning, <1>responsibility
       DEF SelectedClauseRoles, SemanticClauseBinding,
           ClauseSemanticForms, ClauseRoles, DefiningClauses, DerivedClauses,
           ClausesWithRole, ClauseMeet
  <1>sequentialBinding.
      SemanticClauseBinding(
          "state-safety", {TRUE}, RegistrySchemaClauses["EX-SEQ-SERIAL"],
          SelectedClauseRoles("EX-SEQ-SERIAL"),
          [clause \in RegistrySchemaClauses["EX-SEQ-SERIAL"] |->
              SelectedClauseMeaning[clause]],
          IF SelectedResponsibilityHolds["EX-SEQ-SERIAL"] THEN {TRUE} ELSE {},
          {TRUE}, [clause \in {} |-> {}], [clause \in {} |-> {}])
    BY Zenon, <1>registry, <1>meaning, <1>responsibility
       DEF SelectedClauseRoles, SemanticClauseBinding,
           ClauseSemanticForms, ClauseRoles, DefiningClauses, DerivedClauses,
           ClausesWithRole, ClauseMeet
  <1> QED
    BY Zenon, <1>registry, <1>budgetBinding, <1>sequentialBinding
       DEF SelectedSchemaClauseBindingHeld

THEOREM SelectedSchemaClauseBindingSafety ==
    Spec => []SelectedSchemaClauseBindingHeld
BY SelectedCatalogPredicatesSafety, SelectedPredicatesImplyClauseBinding, PTL

THEOREM CatalogActionBindingExact == Next <=> BoundNext
BY SMT
   DEF Next, BoundNext, BudgetStep, SequentialStep,
       CatalogBehaviors, DecisiveBehaviors, BudgetBehaviors,
       SequentialBehaviors, BoundBehaviorStep, BoundBudgetAction,
       BoundSequentialAction, BudgetContract!Next, SequentialContract!Next,
       budgetVars, sequentialVars

THEOREM BoundBehaviorSafety ==
    \A behavior \in CatalogBehaviors :
      ProductInvariant /\ BoundBehaviorStep(behavior) => ProductInvariant'
BY SMT, CatalogActionBindingExact, NextProductInvariant DEF BoundNext

THEOREM BudgetBehaviorPreservesSequentialState ==
    \A behavior \in BudgetBehaviors :
      BoundBehaviorStep(behavior) => UNCHANGED sequentialVars
BY DEF BoundBehaviorStep

THEOREM SequentialBehaviorPreservesBudgetState ==
    \A behavior \in SequentialBehaviors \cup {"sequential-done"} :
      BoundBehaviorStep(behavior) => UNCHANGED budgetVars
BY SMT DEF BoundBehaviorStep, BudgetBehaviors, SequentialBehaviors

====
