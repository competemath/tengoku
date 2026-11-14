import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusHyperbola
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusBoundary
import Tengoku.Twinprime.TwinPrime.Analytic.SmoothingLimits
import Tengoku.Twinprime.TwinPrime.Analytic.TypeICorrection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The classical Möbius inputs from a single ordinary Mertens estimate

`MertensLogSix` records the ordinary quantitative cancellation estimate. It
is an input to the bridges in this file; `PrimeToMertens.lean` derives it
from the named BV hypothesis. All bridges
from that ordinary summatory estimate to the two odd totient limits are
proved, including the boundary constants and the existing twin-prime product.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/-- The ordinary quantitative Mertens estimate, used as an input here and
derived from BV in `PrimeToMertens.lean`.-/
def MertensLogSix : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t : ℕ in atTop,
    |mertensSum t| ≤ K * t / (Real.log t) ^ 6

theorem MertensLogSix.tendsto_normalized_log_sq (hM : MertensLogSix) :
    Tendsto (fun t : ℕ => normalizedMoebiusSum t * (Real.log (t + 1)) ^ 2)
      atTop (nhds 0) := by
  obtain ⟨K, hK, hM⟩ := hM
  exact tendsto_normalizedMoebiusSum_log_sq_of_mertens K hK hM

theorem MertensLogSix.tendsto_smoothed_moebius (hM : MertensLogSix) :
    Tendsto smoothedMoebiusSum atTop (nhds 1) := by
  obtain ⟨K, hK, hM⟩ := hM
  exact tendsto_smoothedMoebiusSum_of_mertens_log_six K hK hM

theorem MertensLogSix.tendsto_odd_totient_log_sq (hM : MertensLogSix) :
    Tendsto (fun t : ℕ => oddMoebiusTotientSum t * (Real.log (t + 1)) ^ 2)
      atTop (nhds 0) :=
  tendsto_oddMoebiusTotientSum_log_sq_of_normalized hM.tendsto_normalized_log_sq

theorem MertensLogSix.tendsto_smoothed_totient (hM : MertensLogSix) :
    Tendsto smoothedTotientSum atTop (nhds (2 * twinPrimeConstant)) :=
  tendsto_smoothedTotientSum_of_smoothedMoebius hM.tendsto_smoothed_moebius

end TwinPrime.Analytic
