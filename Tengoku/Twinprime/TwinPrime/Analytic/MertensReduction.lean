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

/--
@isnad1 id=tendsto.1h0v.s6.7c2f20e4bd2b from=translated src=- shape=8944c262 vocab=b38cb123
-/
theorem MertensLogSix.tendsto_normalized_log_sq (hM : MertensLogSix) :
    Tendsto (fun t : ℕ => normalizedMoebiusSum t * (Real.log (t + 1)) ^ 2)
      atTop (nhds 0) := by
  obtain ⟨K, hK, hM⟩ := hM
  exact tendsto_normalizedMoebiusSum_log_sq_of_mertens K hK hM

/--
@isnad1 id=tendsto.1h0v.s4.c12ecd94ffdf from=translated src=- shape=0250c530 vocab=d9acbff1
-/
theorem MertensLogSix.tendsto_smoothed_moebius (hM : MertensLogSix) :
    Tendsto smoothedMoebiusSum atTop (nhds 1) := by
  obtain ⟨K, hK, hM⟩ := hM
  exact tendsto_smoothedMoebiusSum_of_mertens_log_six K hK hM

/--
@isnad1 id=tendsto.1h0v.s6.3a90a47277f6 from=translated src=- shape=8944c262 vocab=4c05f794
-/
theorem MertensLogSix.tendsto_odd_totient_log_sq (hM : MertensLogSix) :
    Tendsto (fun t : ℕ => oddMoebiusTotientSum t * (Real.log (t + 1)) ^ 2)
      atTop (nhds 0) :=
  tendsto_oddMoebiusTotientSum_log_sq_of_normalized hM.tendsto_normalized_log_sq

/--
@isnad1 id=tendsto.1h0v.s5.65c23d3ce25f from=translated src=- shape=3d073d9d vocab=28a05cae
-/
theorem MertensLogSix.tendsto_smoothed_totient (hM : MertensLogSix) :
    Tendsto smoothedTotientSum atTop (nhds (2 * twinPrimeConstant)) :=
  tendsto_smoothedTotientSum_of_smoothedMoebius hM.tendsto_smoothed_moebius

end TwinPrime.Analytic
