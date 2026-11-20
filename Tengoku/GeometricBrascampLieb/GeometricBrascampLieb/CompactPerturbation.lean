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
/--
@isnad1 id=continuo.0h1v.s4.f1268ee8cb26 from=translated src=- shape=cadbfeb1 vocab=715c45e8
-/
theorem unitTent_continuous : Continuous (unitTent (E := E)) := by unfold unitTent; fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=le.0h2v.s4.39bf51ceddb7 from=translated src=- shape=ad4abcc1 vocab=c5925fd6
-/
theorem unitTent_nonneg (x : E) : 0 ≤ unitTent x := le_max_left _ _

omit [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=hascompa.0h1v.s5.37c53cdca64a from=translated src=- shape=70ededd8 vocab=d36a70a7
-/
theorem unitTent_hasCompactSupport : HasCompactSupport (unitTent (E := E)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) 1)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hx (max_eq_left (by linarith : 1-‖x‖ ≤ 0))

/--
@isnad1 id=integrab.0h1v.s6.609dce0dda3d from=translated src=- shape=79897487 vocab=bafd4265
-/
theorem unitTent_integrable : Integrable (unitTent (E := E)) :=
  unitTent_continuous.integrable_of_hasCompactSupport unitTent_hasCompactSupport

/--
@isnad1 id=lt.0h1v.s6.31ad9dd624d7 from=translated src=- shape=15fa37d9 vocab=2eeaed90
-/
theorem unitTent_integral_pos : 0 < ∫ x : E, unitTent x :=
  integral_pos_of_integrable_nonneg_nonzero unitTent_continuous unitTent_integrable
    unitTent_nonneg (x := (0 : E)) (by simp [unitTent])

def compactPerturbation (f : E → ℝ) (e : ℝ) (x : E) : ℝ := f x+e*unitTent x

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=continuo.1h3v.s5.548bfe3b5a14 from=translated src=- shape=6b09dfb9 vocab=bbd3eb4d
-/
theorem compactPerturbation_continuous {f : E → ℝ} (hf : Continuous f) (e : ℝ) :
    Continuous (compactPerturbation f e) := hf.add (continuous_const.mul unitTent_continuous)

omit [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=hascompa.1h3v.s6.7397bc08b78b from=translated src=- shape=67f76975 vocab=f20dd7c3
-/
theorem compactPerturbation_hasCompactSupport {f : E → ℝ} (hf : HasCompactSupport f) (e : ℝ) :
    HasCompactSupport (compactPerturbation f e) := hf.add unitTent_hasCompactSupport.mul_left

/--
@isnad1 id=eq.1h3v.s7.fa26234493f0 from=translated src=- shape=a4b1380b vocab=a6e1d5ba
-/
theorem integral_compactPerturbation {f : E → ℝ} (hf : Integrable f) (e : ℝ) :
    (∫ x, compactPerturbation f e x) = (∫ x, f x)+e*(∫ x : E, unitTent x) := by
  change (∫ x, f x+e*unitTent x) = _
  rw [integral_add hf (unitTent_integrable.const_mul e), integral_const_mul]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=le.1h4v.s5.8a7ec20b647f from=translated src=- shape=70cc57e9 vocab=b7e0903c
-/
theorem le_compactPerturbation (f : E → ℝ) {e : ℝ} (he : 0 ≤ e) (x : E) :
    f x ≤ compactPerturbation f e x := le_add_of_nonneg_right (mul_nonneg he (unitTent_nonneg x))

/--
@isnad1 id=lt.3h3v.s7.fcfc459a64cc from=translated src=- shape=92e116d6 vocab=21fc5497
-/
theorem integral_compactPerturbation_pos {f : E → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) {e : ℝ} (he : 0 < e) :
    0 < ∫ x, compactPerturbation f e x := by
  rw [integral_compactPerturbation hf]
  exact add_pos_of_nonneg_of_pos (integral_nonneg hf0) (mul_pos he unitTent_integral_pos)

end GeometricBrascampLieb
