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
