import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1WordBlocks
import Tengoku.Seed.Analysis.SpecificLimits.Normed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The geometric word series in ℓ¹

For `‖x‖ < ‖s‖` the vector with coordinates `(s⁻¹)^n * ∏ i, x (a i)` on words `a` of length
`n` lies in ℓ¹(Words I, K) and is the sum of the word blocks applied to `x`. This is the map
`g` in the proof of Theorem 4.5(2). The scalar field need not be complete.
-/

open scoped lp BigOperators
open Filter Topology

namespace L1Coordinates

variable {K I : Type*} [NontriviallyNormedField K]

theorem word_ratio_lt_one {s : K} {x : L1 K I} (hx : ‖x‖ < ‖s‖) :
    ‖s⁻¹‖ * ‖x‖ < 1 := by
  rw [norm_inv, inv_mul_eq_div]
  exact (div_lt_one (lt_of_le_of_lt (norm_nonneg x) hx)).2 hx

theorem hasSum_norm_word_coordinates (s : K) (x : L1 K I) (n : ℕ) :
    HasSum (fun a : Fin n → I => ‖(s⁻¹)^n * ∏ i, x (a i)‖)
      ((‖s⁻¹‖ * ‖x‖)^n) := by
  have h := (hasSum_prod_norm n (fun _ => x)).mul_left (‖s⁻¹‖ ^ n)
  simpa [norm_mul, norm_pow, norm_prod, mul_pow] using h

theorem memℓp_word_coordinates {s : K} {x : L1 K I} (hx : ‖x‖ < ‖s‖) :
    Memℓp (fun a : Words I => (s⁻¹)^a.1 * ∏ i, x (a.2 i)) 1 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).2
  refine ⟨fun n => (hasSum_norm_word_coordinates s x n).summable, ?_⟩
  simpa only [(hasSum_norm_word_coordinates s x _).tsum_eq] using
    summable_geometric_of_norm_lt_one
      (show ‖‖s⁻¹‖ * ‖x‖‖ < 1 by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact word_ratio_lt_one hx)

/-- The word vector of `x`, set to zero when `‖x‖ ≥ ‖s‖`.-/
noncomputable def geometricWordVector (s : K) (x : L1 K I) : L1 K (Words I) :=
  if hx : ‖x‖ < ‖s‖ then
    ⟨fun a => (s⁻¹)^a.1 * ∏ i, x (a.2 i), memℓp_word_coordinates hx⟩
  else 0

theorem geometricWordVector_apply {s : K} {x : L1 K I} (hx : ‖x‖ < ‖s‖)
    (n : ℕ) (a : Fin n → I) :
    geometricWordVector s x ⟨n, a⟩ = (s⁻¹)^n * ∏ i, x (a i) := by
  simp [geometricWordVector, hx]

@[simp]
theorem geometricWordVector_of_not_lt {s : K} {x : L1 K I} (hx : ¬‖x‖ < ‖s‖) :
    geometricWordVector s x = 0 := by
  simp [geometricWordVector, hx]

theorem geometricWordVector_apply_zero {s : K} {x : L1 K I} (hx : ‖x‖ < ‖s‖)
    (a : Fin 0 → I) : geometricWordVector s x ⟨0, a⟩ = 1 := by
  simp [geometricWordVector_apply hx]

end L1Coordinates
