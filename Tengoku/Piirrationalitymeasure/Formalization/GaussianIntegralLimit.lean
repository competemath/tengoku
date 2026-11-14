import Tengoku.Piirrationalitymeasure.Formalization.GaussianPowerLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Gaussian limits for integrals of powers, with domination on expanding intervals. -/

namespace PiIrrationality

open MeasureTheory Filter
open scoped Topology

noncomputable def scaledPower (f : ℝ → ℂ) (T : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  (Set.Icc (-T * Real.sqrt (n : ℝ)) (T * Real.sqrt (n : ℝ))).indicator
    (fun u => f ((Real.sqrt (n : ℝ))⁻¹ * u) ^ n) u

theorem scaledPower_norm_bound {f : ℝ → ℂ} {T c : ℝ}
    (hb : ∀ t ∈ Set.Icc (-T) T, ‖f t‖ ≤ Real.exp (-c * t ^ 2))
    {n : ℕ} (hn : 0 < n) (u : ℝ) : ‖scaledPower f T n u‖ ≤ Real.exp (-c * u ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  by_cases hu : u ∈ Set.Icc (-T * Real.sqrt (n : ℝ)) (T * Real.sqrt (n : ℝ))
  · rw [scaledPower, Set.indicator_of_mem hu, norm_pow]
    have huabs : |u| ≤ T * Real.sqrt (n : ℝ) :=
      abs_le.mpr (by simpa only [Set.mem_Icc, neg_mul] using hu)
    have ht : (Real.sqrt (n : ℝ))⁻¹ * u ∈ Set.Icc (-T) T := by
      apply abs_le.mp
      rw [abs_mul, abs_inv, abs_of_pos hs, inv_mul_eq_div, div_le_iff₀ hs]
      exact huabs
    apply (pow_le_pow_left₀ (norm_nonneg _) (hb _ ht) n).trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [mul_pow, inv_pow, Real.sq_sqrt hn'.le]
    field_simp
  · rw [scaledPower, Set.indicator_of_notMem hu, norm_zero]
    exact (Real.exp_pos _).le

theorem scaledPower_integral {f : ℝ → ℂ} {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) :
    (∫ u : ℝ, scaledPower f T n u) =
      (Real.sqrt (n : ℝ) : ℂ) * ∫ t in -T..T, f t ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hab : -T * Real.sqrt (n : ℝ) ≤ T * Real.sqrt (n : ℝ) := by
    nlinarith [mul_pos hT hs]
  unfold scaledPower
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_mul_left (fun t => f t ^ n) (inv_ne_zero hs.ne')]
  have ha : (Real.sqrt (n : ℝ))⁻¹ * (-T * Real.sqrt (n : ℝ)) = -T := by field_simp
  have hb : (Real.sqrt (n : ℝ))⁻¹ * (T * Real.sqrt (n : ℝ)) = T := by field_simp
  rw [ha, hb, inv_inv, Complex.real_smul]

theorem integral_complex_gaussian (v : ℝ) :
    (∫ u : ℝ, Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2)) =
      (Real.sqrt (2 * Real.pi / v) : ℂ) := by
  have he (u : ℝ) : Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2) =
      (Real.exp (-(v / 2) * u ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [integral_complex_ofReal, integral_gaussian]
  congr 2
  ring

theorem gaussian_integral_power_limit {f : ℝ → ℂ} {T c v : ℝ}
    (hT : 0 < T) (hc : 0 < c) (hf : Continuous f)
    (hb : ∀ t ∈ Set.Icc (-T) T, ‖f t‖ ≤ Real.exp (-c * t ^ 2))
    (hl : ∀ u : ℝ, Tendsto (fun n : ℕ => f ((Real.sqrt (n : ℝ))⁻¹ * u) ^ n) atTop
      (𝓝 (Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2)))) :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) * ∫ t in -T..T, f t ^ n) atTop
      (𝓝 (Real.sqrt (2 * Real.pi / v) : ℂ)) := by
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (scaledPower f T n) := by
    apply Filter.Eventually.of_forall
    intro n
    unfold scaledPower
    exact ((hf.comp (by fun_prop)).pow n).aestronglyMeasurable.indicator measurableSet_Icc
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ u : ℝ, ‖scaledPower f T n u‖ ≤ Real.exp (-c * u ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact Filter.Eventually.of_forall (scaledPower_norm_bound hb hn)
  have hpoint : ∀ᵐ u : ℝ, Tendsto (fun n : ℕ => scaledPower f T n u) atTop
      (𝓝 (Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2))) := by
    apply Filter.Eventually.of_forall
    intro u
    have ht : Tendsto (fun n : ℕ => T * Real.sqrt (n : ℝ)) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hT
    apply (hl u).congr'
    filter_upwards [ht.eventually (eventually_ge_atTop |u|)] with n hn
    have hu : u ∈ Set.Icc (-T * Real.sqrt (n : ℝ)) (T * Real.sqrt (n : ℝ)) := by
      simpa only [Set.mem_Icc, neg_mul] using abs_le.mp hn
    rw [scaledPower, Set.indicator_of_mem hu]
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => Real.exp (-c * u ^ 2)) hmeas hbound (integrable_exp_neg_mul_sq hc) hpoint
  rw [integral_complex_gaussian] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact scaledPower_integral hT hn

end PiIrrationality
