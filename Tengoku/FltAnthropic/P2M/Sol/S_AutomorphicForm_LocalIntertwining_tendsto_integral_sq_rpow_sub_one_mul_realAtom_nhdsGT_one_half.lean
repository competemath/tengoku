import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half

set_option autoImplicit false

open MeasureTheory Filter Topology

noncomputable section

namespace ARCHA4R

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
@isnad1 id=eq.0h3v.s6.d9b239f076fb from=translated src=- shape=fd7727c9 vocab=3455cbe9
-/
theorem norm_atom (k : ℤ) (σ x : ℝ) : ‖atom k σ x‖ = (1 + x ^ 2) ^ (-(σ + 1 / 2)) := by
  rw [atom, norm_mul, norm_zpow, norm_phase, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x)]
  congr 1
  simp

/--
@isnad1 id=continuo.0h0v.s6.d46f8ef2ed7d from=translated src=- shape=255ddb1a vocab=26ac8894
-/
theorem continuous_phase : Continuous fun x : ℝ => (((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun x => ?_
  exact_mod_cast (Real.sqrt_pos.mpr (one_add_sq_pos x)).ne'

/--
@isnad1 id=continuo.0h2v.s4.138c17e110e5 from=translated src=- shape=a17f733d vocab=2220398b
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
@isnad1 id=le.0h3v.s6.5ee1acfca70d from=translated src=- shape=acb0adc4 vocab=cef4cf1d
-/
theorem sq_le (c' d' x : ℝ) : (c' * x + d') ^ 2 ≤ (c' ^ 2 + d' ^ 2) * (1 + x ^ 2) := by
  nlinarith [sq_nonneg (c' - d' * x)]

/--
@isnad1 id=le.3h2v.s5.6ff54dce4287 from=translated src=- shape=ca2ebdbc vocab=c5f81665
-/
theorem rpow_le_max (K t : ℝ) (hK : 0 ≤ K) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : K ^ t ≤ max 1 K := by
  rcases le_or_gt K 1 with h | h
  · exact (Real.rpow_le_one hK h ht0).trans (le_max_left _ _)
  · refine (Real.rpow_le_rpow_of_exponent_le h.le ht1).trans ?_
    rw [Real.rpow_one]; exact le_max_right _ _

/--
@isnad1 id=le.2h5v.s8.84f8f4f29a65 from=translated src=- shape=9a0bc851 vocab=53bda3ea
-/
theorem norm_F_le {c' d' : ℝ} (k : ℤ) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (x : ℝ) :
    ‖((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ) * atom k σ x‖
      ≤ (max 1 (c' ^ 2 + d' ^ 2) + 1) * (1 + x ^ 2)⁻¹ := by
  set t : ℝ := σ - 1 / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  set K : ℝ := c' ^ 2 + d' ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hX : 0 < 1 + x ^ 2 := one_add_sq_pos x
  rw [norm_mul, Complex.norm_real, norm_atom]
  have hWt : ((c' * x + d') ^ 2) ^ t ≤ max 1 K * (1 + x ^ 2) ^ t := by
    calc ((c' * x + d') ^ 2) ^ t ≤ (K * (1 + x ^ 2)) ^ t := Real.rpow_le_rpow (sq_nonneg _) (sq_le c' d' x) ht0
      _ = K ^ t * (1 + x ^ 2) ^ t := Real.mul_rpow hK0 hX.le
      _ ≤ max 1 K * (1 + x ^ 2) ^ t :=
          mul_le_mul_of_nonneg_right (rpow_le_max K t hK0 ht0 ht1) (Real.rpow_nonneg hX.le _)
  have habs : ‖((c' * x + d') ^ 2) ^ t - 1‖ ≤ ((c' * x + d') ^ 2) ^ t + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _), norm_one]
  have h1 : (1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2)) = (1 + x ^ 2)⁻¹ := by
    rw [← Real.rpow_add hX, ← Real.rpow_neg_one]; congr 1; rw [ht]; ring
  have h2 : (1 + x ^ 2) ^ (-(σ + 1 / 2)) ≤ (1 + x ^ 2)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) (by linarith)
  have hpos : 0 ≤ (1 + x ^ 2) ^ (-(σ + 1 / 2)) := Real.rpow_nonneg hX.le _
  have hM0 : 0 ≤ max 1 K := le_trans zero_le_one (le_max_left _ _)
  calc ‖((c' * x + d') ^ 2) ^ t - 1‖ * (1 + x ^ 2) ^ (-(σ + 1 / 2))
      ≤ (max 1 K * (1 + x ^ 2) ^ t + 1) * (1 + x ^ 2) ^ (-(σ + 1 / 2)) :=
        mul_le_mul_of_nonneg_right (habs.trans (by linarith [hWt])) hpos
    _ = max 1 K * ((1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2))) + (1 + x ^ 2) ^ (-(σ + 1 / 2)) := by ring
    _ ≤ max 1 K * (1 + x ^ 2)⁻¹ + (1 + x ^ 2)⁻¹ := by rw [h1]; linarith [h2]
    _ = (max 1 K + 1) * (1 + x ^ 2)⁻¹ := by ring

/--
@isnad1 id=tendsto.1h4v.s7.accd34de6e72 from=translated src=- shape=bc45554f vocab=f374d0ab
-/
theorem tendsto_F {c' d' : ℝ} (k : ℤ) {x : ℝ} (hx : c' * x + d' ≠ 0) :
    Tendsto (fun σ : ℝ => ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ) * atom k σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  have hW : (c' * x + d') ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have h1 : Tendsto (fun σ : ℝ => ((c' * x + d') ^ 2) ^ (σ - 1 / 2)) (𝓝[>] (1 / 2 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => ((c' * x + d') ^ 2) ^ t) 0 := Real.continuousAt_const_rpow hW
    have h2 : Tendsto (fun σ : ℝ => σ - 1 / 2) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun σ : ℝ => σ - 1 / 2) (𝓝 (1 / 2 : ℝ)) (𝓝 ((1 / 2 : ℝ) - 1 / 2)) := tendsto_id.sub_const _
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 := hc.tendsto.comp h2
    rw [Real.rpow_zero] at h3
    exact h3
  have h4 : Tendsto (fun σ : ℝ => ‖(((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ)‖) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    have := (tendsto_sub_nhds_zero_iff.mpr h1).norm
    rwa [norm_zero] at this
  refine squeeze_zero_norm' ?_ h4
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [norm_mul, Complex.norm_real, norm_atom]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  have hσ' : (1 / 2 : ℝ) < σ := hσ
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by linarith)

/--
@isnad1 id=tendsto.1h3v.s7.c838ecac9ad5 from=translated src=- shape=9c793fd5 vocab=a59b19ba
-/
theorem main (c' d' : ℝ) (h : c' ≠ 0 ∨ d' ≠ 0) (k : ℤ) :
    Tendsto (fun σ : ℝ =>
        ∫ x : ℝ, ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ) * atom k σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  have hIoc : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ), σ ∈ Set.Ioc (1 / 2 : ℝ) 1 := Ioc_mem_nhdsGT (by norm_num)
  have hae : ∀ᵐ x : ℝ, c' * x + d' ≠ 0 := by
    rcases eq_or_ne c' 0 with hc | hc
    · refine ae_of_all _ fun x => ?_
      rw [hc, zero_mul, zero_add]
      exact h.resolve_left (not_not.mpr hc)
    · have hsub : {x : ℝ | ¬(c' * x + d' ≠ 0)} ⊆ {-d' / c'} := fun x hx => by
        simp only [Set.mem_ofPred_eq, not_not] at hx
        rw [Set.mem_singleton_iff, eq_div_iff hc]
        linarith
      exact ae_iff.2 (measure_mono_null hsub (measure_singleton _))
  rw [show (0 : ℂ) = ∫ _ : ℝ, (0 : ℂ) by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (max 1 (c' ^ 2 + d' ^ 2) + 1) * (1 + x ^ 2)⁻¹)
    ?_ ?_ ?_ ?_
  · filter_upwards [hIoc] with σ hσ
    have ht0 : 0 ≤ σ - 1 / 2 := by linarith [hσ.1]
    exact (Continuous.mul (Complex.continuous_ofReal.comp
      ((Continuous.rpow_const (by fun_prop) fun x => Or.inr ht0).sub continuous_const)) (continuous_atom k σ)).aestronglyMeasurable
  · filter_upwards [hIoc] with σ hσ
    exact ae_of_all _ fun x => norm_F_le k hσ.1 hσ.2 x
  · exact integrable_inv_one_add_sq.const_mul _
  · filter_upwards [hae] with x hx
    exact tendsto_F k hx

end ARCHA4R

end

/--
@isnad1 id=tendsto.1h3v.s8.4956603621ab from=translated src=- shape=079ef82f vocab=cddeb27a
-/
theorem solution
    (c' d' : ℝ) (_h : c' ≠ 0 ∨ d' ≠ 0) (k : ℤ) :
    Tendsto (fun σ : ℝ =>
        ∫ x : ℝ, ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ)
          * (((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
              * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  exact ARCHA4R.main c' d' _h k
