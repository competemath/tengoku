import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.EntropySeries
import Tengoku

namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiSeries (v : ℝ) : ℝ := ∑' k : ℕ, psiCoeff k * v ^ (2 * (k + 1))

theorem norm_psiSeries_term_le {v : ℝ} (hv : |v| ≤ 1) (k : ℕ) :
    ‖psiCoeff k * v ^ (2 * (k + 1))‖ ≤ psiCoeff k := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (psiCoeff_nonneg k)]
  exact mul_le_of_le_one_right (psiCoeff_nonneg k)
    (pow_le_one₀ (abs_nonneg v) hv)

theorem summable_psi_closed {v : ℝ} (hv : |v| ≤ 1) :
    Summable (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) :=
  Summable.of_norm_bounded summable_psiCoeff (norm_psiSeries_term_le hv)

theorem continuousOn_psiSeries : ContinuousOn psiSeries (Icc (-1) 1) := by
  apply continuousOn_tsum
  · intro k
    fun_prop
  · exact summable_psiCoeff
  · intro k v hv
    exact norm_psiSeries_term_le (abs_le.mpr hv) k

end LeanBlast.CourtadeKumar

end

end OAI
