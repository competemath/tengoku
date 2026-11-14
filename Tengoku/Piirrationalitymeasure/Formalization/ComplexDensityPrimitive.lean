import Tengoku.Piirrationalitymeasure.Formalization.IntegralDecomposition
import Tengoku.Seed.Analysis.Complex.HasPrimitives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A primitive of the actual rational integrand throughout the pole-free disk. -/

namespace PiIrrationality

noncomputable def complexDensity (n : ℕ) (z : ℂ) : ℂ :=
  5 * z ^ (2 * 1857 * n) * (z ^ 4 + 6 * z ^ 2 + 25) ^ (3714 * n) /
    (25 - z ^ 2) ^ (5570 * n + 1)

/--
@isnad1 id=eq.0h2v.s3.496b5942c379 from=translated src=- shape=0f023ca4 vocab=5db46678
-/
theorem complexDensity_vertical (n : ℕ) (s : ℝ) :
    complexDensity n (verticalSegment s) = verticalDensity n s := rfl

/--
@isnad1 id=ne.1h1v.s5.3899513458f3 from=translated src=- shape=afb50d12 vocab=b3dfa31c
-/
theorem complexDensity_den_ne_zero {z : ℂ} (hz : ‖z‖ < 5) : 25 - z ^ 2 ≠ 0 := by
  intro h
  have he : z ^ 2 = (25 : ℂ) := (sub_eq_zero.mp h).symm
  have hn := congrArg norm he
  norm_num only [norm_pow, Complex.norm_ofNat] at hn
  nlinarith [norm_nonneg z]

/--
@isnad1 id=differen.1h2v.s6.25865c4351a2 from=translated src=- shape=d575498d vocab=cd58875f
-/
theorem complexDensity_differentiableAt (n : ℕ) {z : ℂ} (hz : ‖z‖ < 5) :
    DifferentiableAt ℂ (complexDensity n) z := by
  unfold complexDensity
  fun_prop (disch := exact pow_ne_zero _ (complexDensity_den_ne_zero hz))

/--
@isnad1 id=ex.0h1v.s6.2833dea72d47 from=translated src=- shape=c9c80a50 vocab=a91def72
-/
theorem complexDensity_primitive (n : ℕ) :
    ∃ F : ℂ → ℂ, ∀ z : ℂ, ‖z‖ < 5 → HasDerivAt F (complexDensity n z) z := by
  have hd : DifferentiableOn ℂ (complexDensity n) (Metric.ball 0 5) := by
    intro z hz
    exact (complexDensity_differentiableAt n (by simpa using hz)).differentiableWithinAt
  simpa only [Complex.IsExactOn, Metric.mem_ball, dist_zero_right] using hd.isExactOn_ball

/--
@isnad1 id=eq.3h6v.s7.e8e8c6441c41 from=translated src=- shape=38cb5581 vocab=d4b1789f
-/
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
