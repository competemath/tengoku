import Tengoku.AbelFormalization.AbelFormalization.AnalyticGermOneVariable
import Tengoku.AbelFormalization.AbelFormalization.AnalyticGermDimensionZero
import Tengoku.AbelFormalization.AbelFormalization.AnalyticGermComposition
import Tengoku.Seed.RingTheory.RegularLocalRing.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Regularity in zero and one analytic variable

The convergent analytic arguments and the scalar/tuple germ equivalence
establish the full regular Noetherian local-ring assertions in dimensions
zero and one. The corresponding assertions in higher dimensions are not
assumed by these results.
-/

noncomputable section

namespace AbelFormalization

/-- The one-variable result applies to the exact finite-tuple convention used
in the manuscript.
@isnad1 id=isdiscre.0h0v.s10.4d363d7af41d from=translated src=- shape=73f89a9c vocab=909c13a0
-/
instance realAnalyticGermOneIsDiscreteValuationRing :
    IsDiscreteValuationRing (RealAnalyticGerm 1) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing analyticGermOneEquiv

/--
@isnad1 id=isnoethe.0h0v.s11.96cfa8a20550 from=translated src=- shape=73f89a9c vocab=8cb7f7b9
-/
theorem realAnalyticGerm_one_isNoetherian : IsNoetherianRing (RealAnalyticGerm 1) :=
  inferInstance

/--
@isnad1 id=isregula.0h0v.s10.0520579481e6 from=translated src=- shape=73f89a9c vocab=589a90e7
-/
theorem realAnalyticGerm_one_isRegularLocalRing : IsRegularLocalRing (RealAnalyticGerm 1) :=
  inferInstance

/--
@isnad1 id=eq.0h0v.s11.85d12eb8760c from=translated src=- shape=e35ca635 vocab=fa70dab2
-/
theorem realAnalyticGerm_one_ringKrullDim : ringKrullDim (RealAnalyticGerm 1) = 1 := by
  rw [← analyticGermOneEquiv.toRingEquiv.ringKrullDim]
  exact analyticGerm_one_variable_ringKrullDim 0

end AbelFormalization
