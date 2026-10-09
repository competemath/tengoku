module

public import Tengoku

public section

namespace intervalIntegral

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {E : Type*} [NormedAddCommGroup E]

variable [NormedSpace ℝ E]

variable {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ}

/--
@isnad1 id=eq.0h5v.s6.18b631bab69d from=translated src=- shape=7ce4e9d5 vocab=0d55477b
-/
theorem enorm_integral_min_max (f : ℝ → E) :
    ‖∫ x in min a b..max a b, f x ∂μ‖ₑ = ‖∫ x in a..b, f x ∂μ‖ₑ := by
  cases le_total a b <;> simp [*, integral_symm a b]

/--
@isnad1 id=eq.0h5v.s6.d36d80bd8e3d from=translated src=- shape=1b5400ed vocab=f54c88e2
-/
theorem enorm_integral_eq_enorm_integral_uIoc (f : ℝ → E) :
    ‖∫ x in a..b, f x ∂μ‖ₑ = ‖∫ x in Ι a b, f x ∂μ‖ₑ := by
  rw [← enorm_integral_min_max, integral_of_le min_le_max, uIoc]

/--
@isnad1 id=le.0h5v.s6.e02cf8e0c9e5 from=translated src=- shape=b5ed1a6b vocab=1dbb77fc
-/
theorem enorm_integral_le_lintegral_enorm_uIoc : ‖∫ x in a..b, f x ∂μ‖ₑ ≤ ∫⁻ x in Ι a b, ‖f x‖ₑ ∂μ :=
  calc
    ‖∫ x in a..b, f x ∂μ‖ₑ = ‖∫ x in Ι a b, f x ∂μ‖ₑ := enorm_integral_eq_enorm_integral_uIoc f
    _ ≤ ∫⁻ x in Ι a b, ‖f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm f

end intervalIntegral
