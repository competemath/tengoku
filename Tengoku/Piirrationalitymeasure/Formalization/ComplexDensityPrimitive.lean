import Tengoku.Piirrationalitymeasure.Formalization.IntegralDecomposition
import Tengoku.Seed.Analysis.Complex.HasPrimitives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A primitive of the actual rational integrand throughout the pole-free disk. -/

namespace PiIrrationality

noncomputable def complexDensity (n : ℕ) (z : ℂ) : ℂ :=
  5 * z ^ (2 * 1857 * n) * (z ^ 4 + 6 * z ^ 2 + 25) ^ (3714 * n) /
    (25 - z ^ 2) ^ (5570 * n + 1)

theorem complexDensity_vertical (n : ℕ) (s : ℝ) :
    complexDensity n (verticalSegment s) = verticalDensity n s := rfl

theorem complexDensity_den_ne_zero {z : ℂ} (hz : ‖z‖ < 5) : 25 - z ^ 2 ≠ 0 := by
  intro h
  have he : z ^ 2 = (25 : ℂ) := (sub_eq_zero.mp h).symm
  have hn := congrArg norm he
  norm_num only [norm_pow, Complex.norm_ofNat] at hn
  nlinarith [norm_nonneg z]

theorem complexDensity_differentiableAt (n : ℕ) {z : ℂ} (hz : ‖z‖ < 5) :
    DifferentiableAt ℂ (complexDensity n) z := by
  unfold complexDensity
  fun_prop (disch := exact pow_ne_zero _ (complexDensity_den_ne_zero hz))

theorem complexDensity_primitive (n : ℕ) :
    ∃ F : ℂ → ℂ, ∀ z : ℂ, ‖z‖ < 5 → HasDerivAt F (complexDensity n z) z := by
  have hd : DifferentiableOn ℂ (complexDensity n) (Metric.ball 0 5) := by
    intro z hz
    exact (complexDensity_differentiableAt n (by simpa using hz)).differentiableWithinAt
  simpa only [Complex.IsExactOn, Metric.mem_ball, dist_zero_right] using hd.isExactOn_ball

theorem complex_primitive_path_integral {f F : ℂ → ℂ} {g g' : ℝ → ℂ} {a b : ℝ}
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (f (g t)) (g t))
    (hg : ∀ t ∈ Set.uIcc a b, HasDerivAt g (g' t) t)
    (hi : IntervalIntegrable (fun t => f (g t) * g' t) MeasureTheory.volume a b) :
    (∫ t in a..b, f (g t) * g' t) = F (g b) - F (g a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro t ht
  convert! (hF t ht).scomp t (hg t ht) using 1
  simp only [smul_eq_mul, mul_comm]

end PiIrrationality
