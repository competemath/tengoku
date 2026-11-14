import Tengoku.Seed.NumberTheory.Harmonic.Bounds
import Tengoku.Seed.Analysis.Normed.Group.Tannery
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.Algebra.Order.Floor.Semifield

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Harmonic convolution with absolutely summable coefficients

The normalized harmonic kernel is bounded by one on its positive summation
range and tends to one at each fixed positive divisor. Dominated convergence
therefore gives the mass of the positive coefficients, with no logarithmic
moment assumption. Real endpoints and their natural-floor specialization
are both retained.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

/-- The uniform bound that permits domination by the absolute coefficient
alone, without a logarithmically weighted summability assumption.
@isnad1 id=and.3h2v.s7.69d7495b37ed from=translated src=- shape=aa33fee9 vocab=1c5bdc05
-/
theorem harmonic_quotient_normalized_bounds (x : ℝ) (d : ℕ)
    (hx : 1 ≤ x) (hd : 1 ≤ d) (hdx : (d : ℝ) ≤ x) :
    0 ≤ (harmonic ⌊x / d⌋₊ : ℝ) / (1 + Real.log x) ∧
      (harmonic ⌊x / d⌋₊ : ℝ) / (1 + Real.log x) ≤ 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hden : 0 < 1 + Real.log x := by linarith
  have harg : 1 ≤ x / d := (one_le_div hd0).mpr hdx
  have hH : 0 ≤ (harmonic ⌊x / d⌋₊ : ℝ) := by
    simp only [harmonic, Rat.cast_sum]
    exact sum_nonneg (fun _ _ => by positivity)
  refine ⟨div_nonneg hH hden.le, (div_le_one hden).mpr ?_⟩
  apply (harmonic_floor_le_one_add_log (x / d) harg).trans
  apply add_le_add le_rfl
  exact Real.log_le_log (div_pos (lt_of_lt_of_le zero_lt_one hx) hd0)
    (div_le_self (by linarith) (by exact_mod_cast hd))

/-- Every fixed positive divisor preserves the leading logarithm of the
harmonic number, including the floor in its argument.
@isnad1 id=tendsto.1h1v.s6.b371f46264ab from=translated src=- shape=060ae304 vocab=58adb5cd
-/
theorem tendsto_harmonic_quotient_normalized (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun x : ℝ => (harmonic ⌊x / d⌋₊ : ℝ) / (1 + Real.log x))
      atTop (𝓝 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hinv : Tendsto (fun x : ℝ => (1 + Real.log x)⁻¹) atTop (𝓝 0) := by
    apply Tendsto.inv_tendsto_atTop
    simpa only [add_comm] using Real.tendsto_log_atTop.atTop_add
      (tendsto_const_nhds (x := (1 : ℝ)))
  have hlo : Tendsto (fun x : ℝ => 1 - (1 + Real.log d) / (1 + Real.log x))
      atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul (1 + Real.log d))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (max 1 (d : ℝ))] with x hx
    have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hden : 0 < 1 + Real.log x := by have := Real.log_nonneg hx1; linarith
    have hbound := log_le_harmonic_floor (x / d) (div_nonneg hx0.le hd0.le)
    rw [Real.log_div hx0.ne' hd0.ne'] at hbound
    calc
      _ = (Real.log x - Real.log d) / (1 + Real.log x) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right hbound hden.le
  · filter_upwards [eventually_ge_atTop (max 1 (d : ℝ))] with x hx
    exact (harmonic_quotient_normalized_bounds x d ((le_max_left _ _).trans hx)
      hd ((le_max_right _ _).trans hx)).2

/-- General real-endpoint harmonic convolution. The positive finite sum
omits the zero coefficient, so its limiting mass is tsum h minus h(0).
@isnad1 id=tendsto.1h1v.s7.94e0230535a8 from=translated src=- shape=c6c1bc5c vocab=cabee8be
-/
theorem tendsto_real_harmonic_convolution_div_log (h : ℕ → ℝ)
    (hh : Summable (fun d => |h d|)) :
    Tendsto (fun x : ℝ =>
      (∑ d ∈ Ioc 0 ⌊x⌋₊, h d * (harmonic ⌊x / d⌋₊ : ℝ)) / (1 + Real.log x))
      atTop (𝓝 ((∑' d, h d) - h 0)) := by
  classical
  let f : ℝ → ℕ → ℝ := fun x d => if d ∈ Ioc 0 ⌊x⌋₊ then
    h d * ((harmonic ⌊x / d⌋₊ : ℝ) / (1 + Real.log x)) else 0
  let g : ℕ → ℝ := fun d => if d = 0 then 0 else h d
  have hpoint (d : ℕ) : Tendsto (fun x => f x d) atTop (𝓝 (g d)) := by
    by_cases hd : d = 0
    · subst d
      simp [f, g]
    · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
      have ht := (tendsto_harmonic_quotient_normalized d hd1).const_mul (h d)
      simp only [mul_one] at ht
      change Tendsto _ atTop (𝓝 (if d = 0 then 0 else h d))
      rw [ite_eq_right hd]
      apply ht.congr'
      filter_upwards [eventually_ge_atTop (d : ℝ)] with x hx
      have hdmem : d ∈ Ioc 0 ⌊x⌋₊ := mem_Ioc.mpr ⟨hd1, Nat.le_floor hx⟩
      simp only [f, ite_eq_left hdmem]
  have hdom : ∀ᶠ x : ℝ in atTop, ∀ d, ‖f x d‖ ≤ |h d| := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx d
    by_cases hd : d ∈ Ioc 0 ⌊x⌋₊
    · have hd1 := (mem_Ioc.mp hd).1
      have hdx : (d : ℝ) ≤ x :=
        (show (d : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast (mem_Ioc.mp hd).2).trans
          (Nat.floor_le (by linarith))
      obtain ⟨hb0, hb1⟩ := harmonic_quotient_normalized_bounds x d hx hd1 hdx
      simp only [f, ite_eq_left hd, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb0]
      exact mul_le_of_le_one_right (abs_nonneg _) hb1
    · simp only [f, ite_eq_right hd, norm_zero]
      exact abs_nonneg _
  have hlim := tendsto_tsum_of_dominated_convergence hh hpoint hdom
  have hhs : Summable h := summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using hh)
  have hmass : (∑' d, g d) = (∑' d, h d) - h 0 := by
    have hm := hhs.tsum_eq_add_tsum_ite 0
    dsimp only [g]
    linarith
  rw [hmass] at hlim
  apply hlim.congr'
  filter_upwards with x
  rw [tsum_eq_sum (s := Ioc 0 ⌊x⌋₊) (fun d hd => by simp only [f, ite_eq_right hd]), sum_div]
  apply sum_congr rfl
  intro d hd
  simp only [f, ite_eq_left hd, mul_div_assoc]

/-- The common arithmetic-function case has no zero coefficient.
@isnad1 id=tendsto.2h1v.s7.637b9efce21b from=translated src=- shape=4dc6fcac vocab=7cca3d3c
-/
theorem tendsto_real_harmonic_convolution_div_log_of_zero (h : ℕ → ℝ)
    (hh : Summable (fun d => |h d|)) (hzero : h 0 = 0) :
    Tendsto (fun x : ℝ =>
      (∑ d ∈ Ioc 0 ⌊x⌋₊, h d * (harmonic ⌊x / d⌋₊ : ℝ)) / (1 + Real.log x))
      atTop (𝓝 (∑' d, h d)) := by
  simpa only [hzero, sub_zero] using tendsto_real_harmonic_convolution_div_log h hh

/-- Natural endpoints identify the inner floor with natural division.
@isnad1 id=tendsto.1h1v.s7.9f059d2c9914 from=translated src=- shape=6c1d5068 vocab=62e05bec
-/
theorem tendsto_harmonic_convolution_div_log (h : ℕ → ℝ)
    (hh : Summable (fun d => |h d|)) :
    Tendsto (fun z : ℕ =>
      (∑ d ∈ Ioc 0 z, h d * (harmonic (z / d) : ℝ)) / (1 + Real.log z))
      atTop (𝓝 ((∑' d, h d) - h 0)) := by
  simpa only [Function.comp_def, Nat.floor_natCast, Nat.floor_div_natCast] using
    (tendsto_real_harmonic_convolution_div_log h hh).comp tendsto_natCast_atTop_atTop

/--
@isnad1 id=tendsto.2h1v.s7.c7341ce545af from=translated src=- shape=d74bc3aa vocab=4d854db7
-/
theorem tendsto_harmonic_convolution_div_log_of_zero (h : ℕ → ℝ)
    (hh : Summable (fun d => |h d|)) (hzero : h 0 = 0) :
    Tendsto (fun z : ℕ =>
      (∑ d ∈ Ioc 0 z, h d * (harmonic (z / d) : ℝ)) / (1 + Real.log z))
      atTop (𝓝 (∑' d, h d)) := by
  simpa only [hzero, sub_zero] using tendsto_harmonic_convolution_div_log h hh

end TwinPrime.Analytic
