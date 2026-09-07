---- MODULE AssumeGuaranteeRule_Proof ----
EXTENDS AssumeGuaranteeRule, TLAPS

THEOREM AssumeGuaranteeComposition ==
    Contract => Stable(ComposedInvariant, ComposedStep)
BY SMT DEF Contract, WellTyped, Stable, ComposedInvariant, ComposedStep

THEOREM ADischargesBRely ==
    Contract => StepA \subseteq RelyB
BY DEF Contract

THEOREM BDischargesARely ==
    Contract => StepB \subseteq RelyA
BY DEF Contract

====
