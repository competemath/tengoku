import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The norm estimate for a parametrized contour integral used in Lemma 4.4.
The path and exponential phase are abstracted into the integrand and its
pointwise majorant; the estimate is the exact interval-integral statement.
-/

namespace PiIrrationality

theorem intervalIntegral_norm_bound
    {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) 1)
    (hbound : ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖f x‖ ≤ g x) :
    ‖∫ x in (0 : ℝ)..1, f x‖ ≤ ∫ x in (0 : ℝ)..1, g x := by
  apply intervalIntegral.norm_integral_le_of_norm_le (a := (0 : ℝ)) (b := 1)
    (by norm_num)
  · exact Filter.Eventually.of_forall (fun x hx => hbound x hx)
  · exact hg

theorem intervalIntegral_norm_bound_with_factor
    {f : ℝ → ℂ} {A : ℝ → ℝ} {C : ℝ}
    (hA : IntervalIntegrable A MeasureTheory.volume (0 : ℝ) 1)
    (hA_nonneg : ∀ x, 0 ≤ A x)
    (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖f x‖ ≤ A x * C) :
    ‖∫ x in (0 : ℝ)..1, f x‖ ≤
      C * ∫ x in (0 : ℝ)..1, A x := by
  have hAC : IntervalIntegrable (fun x => A x * C) MeasureTheory.volume (0 : ℝ) 1 :=
    hA.mul_const C
  have hraw := intervalIntegral_norm_bound hAC hbound
  have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..1, A x := by
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num) hA_nonneg
  rw [intervalIntegral.integral_mul_const] at hraw
  nlinarith

end PiIrrationality
