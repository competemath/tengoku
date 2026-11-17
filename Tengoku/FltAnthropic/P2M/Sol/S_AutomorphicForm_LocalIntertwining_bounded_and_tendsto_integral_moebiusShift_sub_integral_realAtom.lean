import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real
import Tengoku.FltAnthropic.Theorems.Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom

set_option autoImplicit false

open MeasureTheory Filter Topology

noncomputable section

namespace ARCHW3R

def atom (k : ℤ) (σ x : ℝ) : ℂ :=
  ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))

/--
@isnad1 id=lt.0h1v.s5.17bc9c77b017 from=translated src=- shape=b7e566ab vocab=65df512c
-/
theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

/--
@isnad1 id=eq.0h1v.s6.c9597f056b2d from=translated src=- shape=203dd8d5 vocab=339f4cd1
-/
theorem norm_phase (x : ℝ) : ‖(((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)‖ = 1 := by
  have h1 : ‖((x : ℝ) : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp; ring
  have h2 : Real.sqrt (1 + x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (one_add_sq_pos x)).ne'
  rw [norm_div, h1, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_self h2]

/--
@isnad1 id=eq.0h3v.s6.d144d94037a2 from=translated src=- shape=fd7727c9 vocab=63ca6c5d
-/
theorem norm_atom (k : ℤ) (σ x : ℝ) : ‖atom k σ x‖ = (1 + x ^ 2) ^ (-(σ + 1 / 2)) := by
  rw [atom, norm_mul, norm_zpow, norm_phase, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x)]
  congr 1
  simp

/--
@isnad1 id=le.1h3v.s6.4a1521474758 from=translated src=- shape=456c4e41 vocab=49feb494
-/
theorem norm_atom_le (k : ℤ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) (x : ℝ) : ‖atom k σ x‖ ≤ (1 + x ^ 2)⁻¹ := by
  rw [norm_atom, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) (by linarith)

/--
@isnad1 id=continuo.0h0v.s6.d46f8ef2ed7d from=translated src=- shape=255ddb1a vocab=26ac8894
-/
theorem continuous_phase : Continuous fun x : ℝ => (((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun x => ?_
  exact_mod_cast (Real.sqrt_pos.mpr (one_add_sq_pos x)).ne'

/--
@isnad1 id=continuo.0h2v.s4.9199a9dbf5be from=translated src=- shape=a17f733d vocab=1cc094fa
-/
theorem continuous_atom (k : ℤ) (σ : ℝ) : Continuous (atom k σ) := by
  unfold atom
  refine Continuous.mul (continuous_phase.zpow₀ k fun x => Or.inl ?_) ?_
  · intro h
    have := norm_phase x
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · refine Continuous.cpow (by fun_prop) continuous_const fun x => ?_
    exact_mod_cast Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos x)

/--
@isnad1 id=integrab.1h2v.s6.438996d6d6a0 from=translated src=- shape=d40922b7 vocab=3619e8bb
-/
theorem integrable_atom (k : ℤ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) : Integrable (atom k σ) :=
  Integrable.mono' integrable_inv_one_add_sq (continuous_atom k σ).aestronglyMeasurable
    (ae_of_all _ (norm_atom_le k hσ))

/--
@isnad1 id=le.0h3v.s6.5ee1acfca70d from=translated src=- shape=acb0adc4 vocab=cef4cf1d
-/
theorem sq_le (c' d' x : ℝ) : (c' * x + d') ^ 2 ≤ (c' ^ 2 + d' ^ 2) * (1 + x ^ 2) := by
  nlinarith [sq_nonneg (c' - d' * x)]

/--
@isnad1 id=integrab.1h4v.s7.7a127504e987 from=translated src=- shape=3d0e73a7 vocab=8a16ce34
-/
theorem integrable_weighted (c' d' : ℝ) (k : ℤ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable fun x : ℝ => ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) : ℝ) : ℂ) * atom k σ x := by
  set t : ℝ := σ - 1 / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  set K : ℝ := c' ^ 2 + d' ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (K ^ t)) ?_ (ae_of_all _ fun x => ?_)
  · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ (continuous_atom k σ))
    refine Complex.continuous_ofReal.comp ?_
    exact Continuous.rpow_const (by fun_prop) fun x => Or.inr ht0
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _), norm_atom]
    have h1 : ((c' * x + d') ^ 2) ^ t ≤ K ^ t * (1 + x ^ 2) ^ t := by
      rw [← Real.mul_rpow hK0 (one_add_sq_pos x).le]
      exact Real.rpow_le_rpow (sq_nonneg _) (sq_le c' d' x) ht0
    have h2 : (1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2)) = (1 + x ^ 2)⁻¹ := by
      rw [← Real.rpow_add (one_add_sq_pos x), ← Real.rpow_neg_one]
      congr 1; rw [ht]; ring
    calc ((c' * x + d') ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2))
        ≤ K ^ t * (1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (one_add_sq_pos x).le _)
      _ = K ^ t * (1 + x ^ 2)⁻¹ := by rw [mul_assoc, h2]

/--
@isnad1 id=eq.2h6v.s8.595f97f1f578 from=translated src=- shape=324f7ef3 vocab=9b0f9b5b
-/
theorem jacobian_identity (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) {σ : ℝ} (hσ : 1 / 2 < σ) (x : ℝ) :
    (((|a * d - b * c| / (a + x * c) ^ 2 : ℝ)) : ℂ)
        * (((((-c / Real.sqrt |a * d - b * c|) * ((b + x * d) / (a + x * c)) + d / Real.sqrt |a * d - b * c|) ^ 2)
              ^ (σ - 1 / 2) : ℝ) : ℂ)
      = (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))) := by
  set D : ℝ := |a * d - b * c| with hD
  have hD0 : 0 < D := abs_pos.mpr hdet
  set t : ℝ := a + x * c with ht
  by_cases ht0 : t = 0
  · have hne : (-(2 * (σ : ℂ) + 1)) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    rw [ht0]
    have h1 : ((|(0 : ℝ)| : ℝ) : ℂ) = 0 := by simp
    rw [h1, Complex.zero_cpow hne, mul_zero]
    simp
  · have hs : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD0).ne'
    have hW : ((-c / Real.sqrt D) * ((b + x * d) / t) + d / Real.sqrt D) ^ 2 = D / t ^ 2 := by
      have e1 : (-c / Real.sqrt D) * ((b + x * d) / t) + d / Real.sqrt D = (a * d - b * c) / (t * Real.sqrt D) := by
        field_simp
        rw [ht]; ring
      rw [e1, div_pow, mul_pow, Real.sq_sqrt hD0.le]
      have h2 : (a * d - b * c) ^ 2 = D ^ 2 := by rw [hD, sq_abs]
      have hDne : D ≠ 0 := hD0.ne'
      rw [h2]
      field_simp
    rw [hW]
    have hq : 0 < D / t ^ 2 := div_pos hD0 (by positivity)
    rw [show ((σ : ℂ) + 1 / 2) = ((σ + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      show (-(2 * (σ : ℂ) + 1)) = ((-(2 * σ + 1) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hD0.le, ← Complex.ofReal_cpow (abs_nonneg t), ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc D / t ^ 2 * (D / t ^ 2) ^ (σ - 1 / 2)
        = (D / t ^ 2) ^ (1 + (σ - 1 / 2)) := by rw [Real.rpow_add hq, Real.rpow_one]
      _ = (D / t ^ 2) ^ (σ + 1 / 2) := by congr 1; ring
      _ = D ^ (σ + 1 / 2) / (|t| ^ 2) ^ (σ + 1 / 2) := by rw [Real.div_rpow hD0.le (sq_nonneg t), sq_abs]
      _ = D ^ (σ + 1 / 2) * |t| ^ (-(2 * σ + 1)) := by
          rw [show (|t| ^ 2 : ℝ) = |t| ^ (2 : ℝ) by rw [← Real.rpow_natCast]; norm_num,
            ← Real.rpow_mul (abs_nonneg t), Real.rpow_neg (abs_nonneg t), div_eq_mul_inv]
          congr 2; ring

/--
@isnad1 id=and.1h5v.s8.459a0e272852 from=translated src=- shape=0f7c7de8 vocab=74944334
-/
theorem main (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) (k : ℤ) :
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, atom k σ x‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x : ℝ, (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom k σ ((b + x * d) / (a + x * c)))
          - ∫ x : ℝ, atom k σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  constructor
  · refine ⟨∫ x : ℝ, (1 + x ^ 2)⁻¹, fun σ hσ _ => ?_⟩
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) integrable_inv_one_add_sq
      (ae_of_all _ (norm_atom_le k hσ.le))
  · have hD0 : 0 < |a * d - b * c| := abs_pos.mpr hdet
    have hs : Real.sqrt |a * d - b * c| ≠ 0 := (Real.sqrt_pos.mpr hD0).ne'
    have hcd : (-c / Real.sqrt |a * d - b * c|) ≠ 0 ∨ (d / Real.sqrt |a * d - b * c|) ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not, div_eq_zero_iff, neg_eq_zero, div_eq_zero_iff] at h
      apply hdet
      rw [h.1.resolve_right hs, h.2.resolve_right hs]; ring
    have hA4 := AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half
      (-c / Real.sqrt |a * d - b * c|) (d / Real.sqrt |a * d - b * c|) hcd k
    refine hA4.congr' (eventually_nhdsWithin_of_forall fun σ hσ => ?_)
    have hσ' : 1 / 2 < σ := hσ
    change ∫ x : ℝ, (((((-c / Real.sqrt |a * d - b * c|) * x + d / Real.sqrt |a * d - b * c|) ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ)
        * atom k σ x = _
    have hsplit : (fun x : ℝ => (((((-c / Real.sqrt |a * d - b * c|) * x + d / Real.sqrt |a * d - b * c|) ^ 2)
          ^ (σ - 1 / 2) - 1 : ℝ) : ℂ) * atom k σ x)
        = fun x : ℝ => (((((-c / Real.sqrt |a * d - b * c|) * x + d / Real.sqrt |a * d - b * c|) ^ 2)
          ^ (σ - 1 / 2) : ℝ) : ℂ) * atom k σ x - atom k σ x := by
      funext x; push_cast; ring
    rw [hsplit, integral_sub (integrable_weighted _ _ k hσ') (integrable_atom k hσ'.le)]
    congr 1
    rw [← MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real a b c d hdet
      (fun u => (((((-c / Real.sqrt |a * d - b * c|) * u + d / Real.sqrt |a * d - b * c|) ^ 2) ^ (σ - 1 / 2) : ℝ) : ℂ)
        * atom k σ u)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [← mul_assoc, jacobian_identity a b c d hdet hσ' x]

end ARCHW3R

end

/--
@isnad1 id=other.1h5v.s9.acb7cbc93f07 from=translated src=- shape=cca98f65 vocab=a689b738
-/
theorem solution
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (k : ℤ) :
    let atom : ℝ → ℝ → ℂ := fun σ x =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, atom σ x‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x : ℝ, (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom σ ((b + x * d) / (a + x * c)))
          - ∫ x : ℝ, atom σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  exact ARCHW3R.main a b c d _hdet k
