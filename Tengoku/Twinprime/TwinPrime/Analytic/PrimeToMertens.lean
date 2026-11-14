import Tengoku.Twinprime.TwinPrime.Analytic.PrimeToSelberg
import Tengoku.Twinprime.TwinPrime.Analytic.MertensContraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative Mertens cancellation from the named BV hypothesis

The centered Selberg estimate and its weighted-supremum contraction discharge
the ordinary Mertens input. BV itself remains a hypothesis, and this theorem
does not estimate the shifted bilinear term in the twin-prime decomposition.
-/

noncomputable section

namespace TwinPrime.Analytic

/--
@isnad1 id=mertensl.1h0v.s1.c8d36d78a006 from=translated src=- shape=1d48f1ac vocab=f093a1b4
-/
theorem MaximalBombieriVinogradov.mertensLogSix
    (hBV : MaximalBombieriVinogradov) : MertensLogSix := by
  obtain ⟨c, K, hK, hA⟩ := hBV.centeredSelberg_error
  exact mertensLogSix_of_centeredSelberg_bound c K hK hA

end TwinPrime.Analytic
