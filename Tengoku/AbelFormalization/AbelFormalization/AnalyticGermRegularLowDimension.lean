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
in the manuscript.-/
instance realAnalyticGermOneIsDiscreteValuationRing :
    IsDiscreteValuationRing (RealAnalyticGerm 1) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing analyticGermOneEquiv

theorem realAnalyticGerm_one_isNoetherian : IsNoetherianRing (RealAnalyticGerm 1) :=
  inferInstance

theorem realAnalyticGerm_one_isRegularLocalRing : IsRegularLocalRing (RealAnalyticGerm 1) :=
  inferInstance

theorem realAnalyticGerm_one_ringKrullDim : ringKrullDim (RealAnalyticGerm 1) = 1 := by
  rw [← analyticGermOneEquiv.toRingEquiv.ringKrullDim]
  exact analyticGerm_one_variable_ringKrullDim 0

end AbelFormalization
