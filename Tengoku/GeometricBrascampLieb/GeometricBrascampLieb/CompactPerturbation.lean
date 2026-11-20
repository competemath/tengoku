import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.CompactSupportInequality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Compactly supported perturbations with positive mass -/

noncomputable section
open MeasureTheory

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A nonnegative continuous tent on the unit ball, also valid in dimension zero.-/
def unitTent (x : E) : ℝ := max 0 (1-‖x‖)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem unitTent_continuous : Continuous (unitTent (E := E)) := by unfold unitTent; fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem unitTent_nonneg (x : E) : 0 ≤ unitTent x := le_max_left _ _

omit [MeasurableSpace E] [BorelSpace E] in
theorem unitTent_hasCompactSupport : HasCompactSupport (unitTent (E := E)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) 1)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hx (max_eq_left (by linarith : 1-‖x‖ ≤ 0))

theorem unitTent_integrable : Integrable (unitTent (E := E)) :=
  unitTent_continuous.integrable_of_hasCompactSupport unitTent_hasCompactSupport

theorem unitTent_integral_pos : 0 < ∫ x : E, unitTent x :=
  integral_pos_of_integrable_nonneg_nonzero unitTent_continuous unitTent_integrable
    unitTent_nonneg (x := (0 : E)) (by simp [unitTent])

def compactPerturbation (f : E → ℝ) (e : ℝ) (x : E) : ℝ := f x+e*unitTent x

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compactPerturbation_continuous {f : E → ℝ} (hf : Continuous f) (e : ℝ) :
    Continuous (compactPerturbation f e) := hf.add (continuous_const.mul unitTent_continuous)

omit [MeasurableSpace E] [BorelSpace E] in
theorem compactPerturbation_hasCompactSupport {f : E → ℝ} (hf : HasCompactSupport f) (e : ℝ) :
    HasCompactSupport (compactPerturbation f e) := hf.add unitTent_hasCompactSupport.mul_left

theorem integral_compactPerturbation {f : E → ℝ} (hf : Integrable f) (e : ℝ) :
    (∫ x, compactPerturbation f e x) = (∫ x, f x)+e*(∫ x : E, unitTent x) := by
  change (∫ x, f x+e*unitTent x) = _
  rw [integral_add hf (unitTent_integrable.const_mul e), integral_const_mul]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem le_compactPerturbation (f : E → ℝ) {e : ℝ} (he : 0 ≤ e) (x : E) :
    f x ≤ compactPerturbation f e x := le_add_of_nonneg_right (mul_nonneg he (unitTent_nonneg x))

theorem integral_compactPerturbation_pos {f : E → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) {e : ℝ} (he : 0 < e) :
    0 < ∫ x, compactPerturbation f e x := by
  rw [integral_compactPerturbation hf]
  exact add_pos_of_nonneg_of_pos (integral_nonneg hf0) (mul_pos he unitTent_integral_pos)

end GeometricBrascampLieb
