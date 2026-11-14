import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Quadratic characteristic expansions, Gaussian domination, and the limit of powers. -/

namespace PiIrrationality

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

/--
@isnad1 id=islittle.2h3v.s8.6e8d6ce043ec from=translated src=- shape=9e852a53 vocab=8bff90ab
-/
theorem centered_charFun_taylor {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 2 P) (h0 : ∫ ω, X ω ∂P = 0) :
    (fun t : ℝ => charFun (P.map X) t -
      (1 - (↑(∫ ω, X ω ^ 2 ∂P) : ℂ) * (t : ℂ) ^ 2 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hm : MemLp id 2 (P.map X) :=
    (memLp_map_measure_iff (by fun_prop) hX.aemeasurable).mpr hX
  have hp (t : ℝ) : taylorWithinEval (charFun (P.map X)) 2 Set.univ 0 t =
      1 - (↑(∫ ω, X ω ^ 2 ∂P) : ℂ) * (t : ℂ) ^ 2 / 2 := by
    rw [taylorWithinEval_charFun_two_zero hX.aemeasurable hm, h0]
    simp
  simp_rw [← hp]
  simpa only [sub_zero] using taylor_isLittleO_univ (x₀ := 0) (contDiff_charFun hm)

/--
@isnad1 id=eventual.2h2v.s7.ea46cc60a786 from=translated src=- shape=93e03081 vocab=e009213c
-/
theorem quadratic_expansion_gaussian_bound {f : ℝ → ℂ} {v : ℝ} (hv : 0 < v)
    (h : (fun t : ℝ => f t - (1 - (v : ℂ) * (t : ℂ) ^ 2 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2)) :
    ∀ᶠ t : ℝ in 𝓝 0, ‖f t‖ ≤ Real.exp (-(v / 4) * t ^ 2) := by
  have he := h.def (show 0 < v / 4 by positivity)
  have hp : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 - v * t ^ 2 / 2 := by
    have hc : Continuous (fun t : ℝ => 1 - v * t ^ 2 / 2) := by fun_prop
    exact hc.continuousAt.eventually
      (lt_mem_nhds (show (0 : ℝ) < 1 - v * 0 ^ 2 / 2 by norm_num))
  filter_upwards [he, hp] with t he hp
  have hn : ‖(1 - (v : ℂ) * (t : ℂ) ^ 2 / 2)‖ = 1 - v * t ^ 2 / 2 := by
    rw [show (1 - (v : ℂ) * (t : ℂ) ^ 2 / 2) = ((1 - v * t ^ 2 / 2 : ℝ) : ℂ) by
      push_cast; rfl]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  have ht : ‖t ^ 2‖ = t ^ 2 := Real.norm_of_nonneg (sq_nonneg t)
  rw [ht] at he
  calc
    ‖f t‖ ≤ ‖f t - (1 - (v : ℂ) * (t : ℂ) ^ 2 / 2)‖ +
        ‖1 - (v : ℂ) * (t : ℂ) ^ 2 / 2‖ := norm_le_norm_sub_add _ _
    _ ≤ v / 4 * t ^ 2 + (1 - v * t ^ 2 / 2) := by rw [hn]; linarith
    _ = 1 + (-(v / 4) * t ^ 2) := by ring
    _ ≤ Real.exp (-(v / 4) * t ^ 2) := by
      simpa only [add_comm] using Real.add_one_le_exp (-(v / 4) * t ^ 2)

/-- The variance-parameter version of mathlib's characteristic-function power limit.
@isnad1 id=tendsto.1h3v.s7.dbc615d32ed6 from=translated src=- shape=f6982a35 vocab=77a60ff1
-/
theorem quadratic_expansion_power_limit {f : ℝ → ℂ} {v : ℝ}
    (h : (fun t : ℝ => f t - (1 - (v : ℂ) * (t : ℂ) ^ 2 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2)) (u : ℝ) :
    Tendsto (fun n : ℕ => f ((Real.sqrt (n : ℝ))⁻¹ * u) ^ n) atTop
      (𝓝 (Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2))) := by
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div
  suffices (fun n : ℕ => f ((Real.sqrt (n : ℝ))⁻¹ * u) -
      (1 + (-((v : ℂ) * (((Real.sqrt (n : ℝ))⁻¹ * u : ℝ) : ℂ) ^ 2 / 2))))
      =o[atTop] (fun n : ℕ => ((Real.sqrt (n : ℝ))⁻¹ * u) ^ 2) by
    have hn : (fun n : ℕ => ‖1 / (n : ℂ)‖) = fun n : ℕ => ‖1 / (n : ℝ)‖ := by simp
    rw [← isLittleO_norm_right, hn, isLittleO_norm_right]
    apply IsLittleO.of_const_mul_right (c := u ^ 2)
    convert! this using 4 with n <;> norm_cast <;> simp [field]
  have ht : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ * u) atTop (𝓝 0) := by
    rw [← zero_mul u]
    exact (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).mul_const u
  convert! h.comp_tendsto ht using 2

end PiIrrationality
