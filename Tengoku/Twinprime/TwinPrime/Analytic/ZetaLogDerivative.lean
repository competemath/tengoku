import Tengoku.Twinprime.TwinPrime.Analytic.ZetaContinuation
import Tengoku.Seed.Analysis.Complex.Liouville

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The regularized zeta logarithmic derivative

The exact logarithmic derivative identity retains the principal pole. The
positive-half-plane truncation estimate gives explicit growth and Cauchy
derivative bounds for the entire regularization, including at the pole.
-/

noncomputable section

open Metric

namespace TwinPrime.Analytic

theorem deriv_regularizedRiemannZeta_of_ne_one (s : ℂ) (hs : s ≠ 1) :
    deriv regularizedRiemannZeta s =
      (s - 1) * deriv riemannZeta s + riemannZeta s := by
  simpa only [regularizedRiemannZeta, DirichletCharacter.LFunctionTrivChar,
    DirichletCharacter.LFunction_modOne_eq] using
    DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs

/-- The pole term is explicit; the regularization must be nonzero only at
the point where its logarithmic derivative is evaluated.-/
theorem neg_zeta_logDerivative_eq_pole_sub_regularized (s : ℂ) (hs : s ≠ 1)
    (hZ : regularizedRiemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      1 / (s - 1) - deriv regularizedRiemannZeta s / regularizedRiemannZeta s := by
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hz : riemannZeta s ≠ 0 := by
    rw [regularizedRiemannZeta_apply_of_ne_one s hs] at hZ
    exact (mul_ne_zero_iff.mp hZ).2
  rw [deriv_regularizedRiemannZeta_of_ne_one s hs,
    regularizedRiemannZeta_apply_of_ne_one s hs]
  field_simp
  ring

@[simp] theorem regularizedZetaPartialSum_cutoff_one (s : ℂ) :
    regularizedZetaPartialSum s 1 = s := by
  simp [regularizedZetaPartialSum]

theorem norm_regularizedRiemannZeta_sub_self_le (s : ℂ) (hs : 0 < s.re) :
    ‖regularizedRiemannZeta s - s‖ ≤ ‖s - 1‖ * (‖s‖ / s.re) := by
  simpa using norm_regularizedRiemannZeta_sub_partialSum_le 1 (by norm_num) s hs

def regularizedZetaGrowthBudget (δ H : ℝ) : ℝ := H + (H + 1) * (H / δ)

theorem norm_regularizedRiemannZeta_le_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    ‖regularizedRiemannZeta s‖ ≤ regularizedZetaGrowthBudget s.re ‖s‖ := by
  have ht := norm_regularizedRiemannZeta_sub_self_le s hs
  have hn := norm_add_le (regularizedRiemannZeta s - s) s
  rw [sub_add_cancel] at hn
  have hsub : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s (1 : ℂ)
  have hm := mul_le_mul_of_nonneg_right hsub (div_nonneg (norm_nonneg s) hs.le)
  unfold regularizedZetaGrowthBudget
  linarith

theorem norm_regularizedRiemannZeta_le_on_re_norm (δ H : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hs : δ ≤ s.re) (hH : ‖s‖ ≤ H) :
    ‖regularizedRiemannZeta s‖ ≤ regularizedZetaGrowthBudget δ H := by
  apply (norm_regularizedRiemannZeta_le_of_re_pos s (hδ.trans_le hs)).trans
  unfold regularizedZetaGrowthBudget
  have hH0 : 0 ≤ H := (norm_nonneg s).trans hH
  gcongr
  exact div_nonneg (norm_nonneg s) (hδ.trans_le hs).le

theorem norm_regularizedRiemannZeta_le_on_closedBall (s : ℂ) (R : ℝ)
    (hR : R < s.re) (z : ℂ) (hz : z ∈ closedBall s R) :
    ‖regularizedRiemannZeta z‖ ≤
      regularizedZetaGrowthBudget (s.re - R) (‖s‖ + R) := by
  have hdist : ‖z - s‖ ≤ R := mem_closedBall_iff_norm.mp hz
  have hre := (abs_le.mp (Complex.abs_re_le_norm (z - s))).1
  simp only [Complex.sub_re] at hre
  apply norm_regularizedRiemannZeta_le_on_re_norm (s.re - R) (‖s‖ + R)
    (by linarith) z
  · linarith
  · exact norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hz)

theorem norm_iteratedDeriv_regularizedRiemannZeta_le (s : ℂ) (R : ℝ)
    (hR0 : 0 < R) (hR : R < s.re) (n : ℕ) :
    ‖iteratedDeriv n regularizedRiemannZeta s‖ ≤
      n.factorial * regularizedZetaGrowthBudget (s.re - R) (‖s‖ + R) / R ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR0
    differentiable_regularizedRiemannZeta.diffContOnCl
  intro z hz
  exact norm_regularizedRiemannZeta_le_on_closedBall s R hR z (sphere_subset_closedBall hz)

theorem norm_deriv_regularizedRiemannZeta_le (s : ℂ) (R : ℝ)
    (hR0 : 0 < R) (hR : R < s.re) :
    ‖deriv regularizedRiemannZeta s‖ ≤
      regularizedZetaGrowthBudget (s.re - R) (‖s‖ + R) / R := by
  simpa using norm_iteratedDeriv_regularizedRiemannZeta_le s R hR0 hR 1

/-- A concrete local bound at the pole follows directly from the cutoff-one
truncation estimate. It does not assume nonvanishing.-/
theorem norm_regularizedRiemannZeta_sub_one_le_two_thirds (s : ℂ)
    (hs : ‖s - 1‖ ≤ 1 / 4) :
    ‖regularizedRiemannZeta s - 1‖ ≤ 2 / 3 := by
  have hre := (abs_le.mp (Complex.abs_re_le_norm (s - 1))).1
  simp only [Complex.sub_re, Complex.one_re] at hre
  have hσ : 3 / 4 ≤ s.re := by linarith
  have hσ0 : 0 < s.re := by linarith
  have hnorm : ‖s‖ ≤ 5 / 4 := by
    have h := norm_add_le (s - 1) (1 : ℂ)
    simp only [sub_add_cancel, norm_one] at h
    linarith
  have hratio : ‖s‖ / s.re ≤ 5 / 3 := by
    apply (div_le_iff₀ hσ0).mpr
    nlinarith
  have ht := norm_regularizedRiemannZeta_sub_self_le s hσ0
  have hm := mul_le_mul hs hratio (div_nonneg (norm_nonneg _) hσ0.le)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hn := norm_add_le (regularizedRiemannZeta s - s) (s - 1)
  rw [sub_add_sub_cancel] at hn
  linarith

theorem one_third_le_norm_regularizedRiemannZeta (s : ℂ)
    (hs : ‖s - 1‖ ≤ 1 / 4) :
    1 / 3 ≤ ‖regularizedRiemannZeta s‖ := by
  have ht := norm_regularizedRiemannZeta_sub_one_le_two_thirds s hs
  have hn := norm_add_le (1 - regularizedRiemannZeta s) (regularizedRiemannZeta s)
  simp only [sub_add_cancel, norm_one, norm_sub_rev (1 : ℂ)] at hn
  linarith

theorem regularizedRiemannZeta_ne_zero_of_norm_sub_one_le (s : ℂ)
    (hs : ‖s - 1‖ ≤ 1 / 4) : regularizedRiemannZeta s ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (one_third_le_norm_regularizedRiemannZeta s hs))

theorem norm_regularizedRiemannZeta_logDerivative_le_forty (s : ℂ)
    (hs : ‖s - 1‖ ≤ 1 / 8) :
    ‖deriv regularizedRiemannZeta s / regularizedRiemannZeta s‖ ≤ 40 := by
  have hd : ‖deriv regularizedRiemannZeta s‖ ≤ 40 / 3 := by
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (f := regularizedRiemannZeta) (c := s) (R := 1 / 8) (C := 5 / 3)
      (by norm_num) differentiable_regularizedRiemannZeta.diffContOnCl
    apply (show (5 / 3 : ℝ) / (1 / 8) = 40 / 3 by norm_num) ▸ hc
    intro z hz
    have hdist : ‖z - s‖ = 1 / 8 := mem_sphere_iff_norm.mp hz
    have hz1 : ‖z - 1‖ ≤ 1 / 4 := by
      have h := norm_add_le (z - s) (s - 1)
      rw [sub_add_sub_cancel, hdist] at h
      linarith
    have ht := norm_regularizedRiemannZeta_sub_one_le_two_thirds z hz1
    have hn := norm_add_le (regularizedRiemannZeta z - 1) (1 : ℂ)
    simp only [sub_add_cancel, norm_one] at hn
    linarith
  have hl := one_third_le_norm_regularizedRiemannZeta s (by linarith)
  rw [norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hl)).mpr
  linarith

/-- An explicit bounded regular part of the negative zeta logarithmic
derivative in a punctured neighborhood of the pole.-/
theorem norm_neg_zeta_logDerivative_sub_pole_le_forty (s : ℂ)
    (hs1 : s ≠ 1) (hs : ‖s - 1‖ ≤ 1 / 8) :
    ‖-deriv riemannZeta s / riemannZeta s - 1 / (s - 1)‖ ≤ 40 := by
  rw [neg_zeta_logDerivative_eq_pole_sub_regularized s hs1
    (regularizedRiemannZeta_ne_zero_of_norm_sub_one_le s (by linarith))]
  simpa only [sub_sub_cancel_left, norm_neg] using
    norm_regularizedRiemannZeta_logDerivative_le_forty s hs

end TwinPrime.Analytic
