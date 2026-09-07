---- MODULE CompetitiveSelectionImplRefinesSpec_Proof ----
EXTENDS CompetitiveSelectionImplRefinesSpec, TLAPS

LEMMA HardInitRefines == Init => H!Init BY DEF Init, H!Init
LEMMA HardNextRefines == [ImplNext]_vars => [H!Next]_(H!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [H!Next]_(H!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, H!vars
  <1>1. CASE HardStep
    BY <1>1 DEF HardStep, ImplHardEvaluate, ImplHardUpdateScore,
                  HardInvariant, HardBest, H!Next, H!Evaluate, H!UpdateScore
  <1>2. CASE SoftStep BY <1>2 DEF SoftStep, H!vars
  <1>3. CASE MutableStep BY <1>3 DEF MutableStep, H!vars
  <1>4. CASE RankedStep BY <1>4 DEF RankedStep, H!vars
  <1>5. CASE ImplRead BY <1>5 DEF ImplRead, vars, H!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5 DEF ImplNext
THEOREM HardRefinementThm == Spec => H!Spec
  BY HardInitRefines, HardNextRefines, PTL DEF Spec, H!Spec

LEMMA SoftInitRefines == Init => S!Init BY DEF Init, S!Init
LEMMA SoftNextRefines == [ImplNext]_vars => [S!Next]_(S!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [S!Next]_(S!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, S!vars
  <1>1. CASE SoftStep
    BY <1>1 DEF SoftStep, ImplSoftAssign, SoftInvariant,
                  S!Next, S!AssignNext
  <1>2. CASE HardStep BY <1>2 DEF HardStep, S!vars
  <1>3. CASE MutableStep BY <1>3 DEF MutableStep, S!vars
  <1>4. CASE RankedStep BY <1>4 DEF RankedStep, S!vars
  <1>5. CASE ImplRead BY <1>5 DEF ImplRead, vars, S!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5 DEF ImplNext
THEOREM SoftRefinementThm == Spec => S!Spec
  BY SoftInitRefines, SoftNextRefines, PTL DEF Spec, S!Spec

LEMMA MutableInitRefines == Init => MS!Init BY DEF Init, MS!Init
LEMMA MutableNextRefines == [ImplNext]_vars => [MS!MutableScoreNext]_(MS!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [MS!MutableScoreNext]_(MS!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, MS!vars
  <1>1. CASE MutableStep
    BY <1>1 DEF MutableStep, ImplMutableAssign, ImplMutableUpdate,
                  MutableInvariant, MS!MutableScoreNext,
                  MS!AssignNext, MS!UpdateScore
  <1>2. CASE HardStep BY <1>2 DEF HardStep, MS!vars
  <1>3. CASE SoftStep BY <1>3 DEF SoftStep, MS!vars
  <1>4. CASE RankedStep BY <1>4 DEF RankedStep, MS!vars
  <1>5. CASE ImplRead BY <1>5 DEF ImplRead, vars, MS!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5 DEF ImplNext
THEOREM MutableRefinementThm == Spec => MS!MutableScoreSpec
  BY MutableInitRefines, MutableNextRefines, PTL
     DEF Spec, MS!MutableScoreSpec

LEMMA RankedInitRefines == Init => R!Init BY DEF Init, R!Init
LEMMA RankedNextRefines == [ImplNext]_vars => [R!Next]_(R!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [R!Next]_(R!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, R!vars
  <1>1. CASE RankedStep
    <2>select. CASE ImplRankedSelect
      <3>sub. ranked_selected' \subseteq Candidates
        BY <2>select DEF ImplRankedSelect, RankedInvariant, R!TypeInvariant
      <3>card. R!Cardinality(ranked_selected') = K
        BY <2>select DEF ImplRankedSelect
      <3>tie. \A c \in ranked_selected' :
                 \A d \in Candidates \ ranked_selected' : R!Better(c, d)
        <4> SUFFICES ASSUME NEW c \in ranked_selected',
                             NEW d \in Candidates \ ranked_selected'
                     PROVE R!Better(c, d)  OBVIOUS
        <4>primedTie. R!Better(c, d)'
          BY <2>select
             DEF ImplRankedSelect, RankedInvariant, R!RankedTieBreak
        <4> QED
          BY <2>select, <4>primedTie
             DEF ImplRankedSelect, R!Better, R!Pos, R!WEnum
      <3>scores. UNCHANGED ranked_scores
        BY <2>select DEF ImplRankedSelect
      <3>next. R!Select
        BY <3>sub, <3>card, <3>tie, <3>scores DEF R!Select
      <3> QED BY <3>next DEF R!Next
    <2>update. CASE ImplRankedUpdate
      BY <2>update DEF ImplRankedUpdate, R!Next, R!UpdateScores
    <2> QED BY <1>1, <2>select, <2>update DEF RankedStep
  <1>2. CASE HardStep BY <1>2 DEF HardStep, R!vars
  <1>3. CASE SoftStep BY <1>3 DEF SoftStep, R!vars
  <1>4. CASE MutableStep BY <1>4 DEF MutableStep, R!vars
  <1>5. CASE ImplRead BY <1>5 DEF ImplRead, vars, R!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5 DEF ImplNext
THEOREM RankedRefinementThm == Spec => R!Spec
  BY RankedInitRefines, RankedNextRefines, PTL DEF Spec, R!Spec

THEOREM HardOriginal == Spec => HardRefinement
  BY HardRefinementThm DEF HardRefinement
THEOREM SoftOriginal == Spec => SoftRefinement
  BY SoftRefinementThm DEF SoftRefinement
THEOREM MutableOriginal == Spec => MutableSoftRefinement
  BY MutableRefinementThm DEF MutableSoftRefinement
THEOREM RankedOriginal == Spec => RankedRefinement
  BY RankedRefinementThm DEF RankedRefinement
====
