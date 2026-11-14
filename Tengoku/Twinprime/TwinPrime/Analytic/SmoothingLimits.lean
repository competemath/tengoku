import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusAbel
import Tengoku.Twinprime.TwinPrime.Analytic.SmoothingSummability
import Tengoku.Seed.Analysis.Normed.Group.Tannery

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transfer of ordinary cancellation through the smoothing correction

These are analytic transfer theorems for the exact finite convolutions. The
ordinary Möbius limits remain explicit inputs; the correction is absolutely
summable and contributes its independently computed Euler-product mass.
-/

noncomputable section

open Finset Filter
open scoped Topology
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

theorem log_sq_nat_le_div_log_sq (U d : ℕ) (hd : 0 < d) :
    (Real.log ((U : ℝ) + 1)) ^ 2 ≤
      2 * ((Real.log ((d : ℝ) + 1)) ^ 2 + (Real.log ((U / d : ℕ) + 1)) ^ 2) := by
  have hprod : U + 1 ≤ (d + 1) * (U / d + 1) := by
    have hmod := Nat.mod_lt U hd
    have hdiv := Nat.mod_add_div U d
    nlinarith
  have hU : 0 < (U : ℝ) + 1 := by positivity
  have hdR : 0 < (d : ℝ) + 1 := by positivity
  have hqR : 0 < (U / d : ℕ) + (1 : ℝ) := by positivity
  have hlog : Real.log ((U : ℝ) + 1) ≤
      Real.log ((d : ℝ) + 1) + Real.log ((U / d : ℕ) + (1 : ℝ)) := by
    calc
      _ ≤ Real.log (((d : ℝ) + 1) * ((U / d : ℕ) + (1 : ℝ))) :=
        Real.log_le_log hU (by exact_mod_cast hprod)
      _ = _ := Real.log_mul hdR.ne' hqR.ne'
  have hnonneg : 0 ≤ Real.log ((U : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) U; linarith)
  have hsq := pow_le_pow_left₀ hnonneg hlog 2
  nlinarith [sq_nonneg (Real.log ((d : ℝ) + 1) - Real.log ((U / d : ℕ) + (1 : ℝ)))]

theorem tendsto_nat_div_atTop (d : ℕ) (hd : 0 < d) :
    Tendsto (fun U : ℕ => U / d) atTop atTop := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := (tendsto_nat_floor_atTop (α := ℝ)).comp
    ((tendsto_div_const_atTop_of_pos hdR).mpr tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def, Nat.floor_div_natCast, Nat.floor_natCast] using h

/-- A fixed divisor preserves square-logarithmic decay with the original endpoint.-/
theorem tendsto_nat_div_mul_log_sq (F : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hF : Tendsto (fun n : ℕ => F n * (Real.log (n + 1)) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun U : ℕ => F (U / d) * (Real.log (U + 1)) ^ 2) atTop (𝓝 0) := by
  have hq := tendsto_nat_div_atTop d hd
  have hzero := (tendsto_of_mul_log_sq_tendsto_zero F hF).comp hq
  have hweight := hF.comp hq
  have hu := ((hzero.abs.mul_const ((Real.log ((d : ℝ) + 1)) ^ 2)).add hweight.abs).const_mul 2
  simp only [abs_zero, zero_mul, add_zero, mul_zero] at hu
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with U
    exact abs_nonneg _
  · filter_upwards with U
    dsimp only [Function.comp_def]
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.log ((U : ℝ) + 1))),
      abs_mul, abs_of_nonneg (sq_nonneg (Real.log ((U / d : ℕ) + (1 : ℝ))))]
    have h := mul_le_mul_of_nonneg_left (log_sq_nat_le_div_log_sq U d hd) (abs_nonneg (F (U / d)))
    nlinarith

theorem exists_bound_of_tendsto_nat (F : ℕ → ℝ) (L : ℝ)
    (hF : Tendsto F atTop (𝓝 L)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |F n| ≤ C := by
  rcases (Metric.isBounded_range_of_tendsto F hF).exists_pos_norm_le with ⟨C, hC, hbound⟩
  exact ⟨C, hC.le, fun n => by simpa only [Real.norm_eq_abs] using hbound (F n) (Set.mem_range_self n)⟩

/-- Absolutely summable divisor weights with a square-logarithmic moment
preserve normalized square-logarithmic cancellation.-/
theorem tendsto_divisorConvolution_mul_log_sq (h F : ℕ → ℝ)
    (hh : Summable (fun d => |h d|))
    (hhlog : Summable (fun d : ℕ => (Real.log ((d : ℝ) + 1)) ^ 2 * |h d|))
    (hF : Tendsto (fun n : ℕ => F n * (Real.log (n + 1)) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun U : ℕ => (∑ d ∈ Ioc 0 U, h d * F (U / d)) *
      (Real.log (U + 1)) ^ 2) atTop (𝓝 0) := by
  classical
  rcases exists_bound_of_tendsto_nat F 0 (tendsto_of_mul_log_sq_tendsto_zero F hF) with
    ⟨C₀, hC₀, hbound₀⟩
  rcases exists_bound_of_tendsto_nat (fun n => F n * (Real.log (n + 1)) ^ 2) 0 hF with
    ⟨C₂, hC₂, hbound₂⟩
  let f : ℕ → ℕ → ℝ := fun U d =>
    if d ∈ Ioc 0 U then h d * (F (U / d) * (Real.log (U + 1)) ^ 2) else 0
  let B : ℕ → ℝ := fun d =>
    2 * (C₀ * (Real.log ((d : ℝ) + 1)) ^ 2 + C₂) * |h d|
  have hB : Summable B := by
    apply (((hhlog.mul_left C₀).add (hh.mul_left C₂)).mul_left 2).congr
    intro d
    dsimp only [B]
    ring
  have hpoint (d : ℕ) : Tendsto (fun U => f U d) atTop (𝓝 0) := by
    by_cases hd : d = 0
    · subst d
      simp [f]
    · have hlim := (tendsto_nat_div_mul_log_sq F d (Nat.pos_of_ne_zero hd) hF).const_mul (h d)
      simp only [mul_zero] at hlim
      apply hlim.congr'
      filter_upwards [eventually_ge_atTop d] with U hU
      simp [f, mem_Ioc, Nat.pos_of_ne_zero hd, hU]
  have hdom : ∀ U d, ‖f U d‖ ≤ B d := by
    intro U d
    by_cases hd : d ∈ Ioc 0 U
    · have hlog := log_sq_nat_le_div_log_sq U d (mem_Ioc.mp hd).1
      have hbd0 := hbound₀ (U / d)
      have hbd2 := hbound₂ (U / d)
      rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.log ((U / d : ℕ) + (1 : ℝ))))] at hbd2
      have hweighted : |F (U / d)| * (Real.log ((U : ℝ) + 1)) ^ 2 ≤
          2 * (C₀ * (Real.log ((d : ℝ) + 1)) ^ 2 + C₂) := by
        have hmul := mul_le_mul_of_nonneg_left hlog (abs_nonneg (F (U / d)))
        have h₀ := mul_le_mul_of_nonneg_right hbd0 (sq_nonneg (Real.log ((d : ℝ) + 1)))
        nlinarith
      simp only [f, ite_eq_left hd, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg (Real.log ((U : ℝ) + 1)))]
      dsimp only [B]
      nlinarith [mul_le_mul_of_nonneg_left hweighted (abs_nonneg (h d))]
    · simp only [f, ite_eq_right hd, norm_zero]
      dsimp [B]
      positivity
  have hlim := tendsto_tsum_of_dominated_convergence hB hpoint
    (Eventually.of_forall hdom)
  simp only [tsum_zero] at hlim
  apply hlim.congr'
  filter_upwards with U
  rw [tsum_eq_sum (s := Ioc 0 U) (fun d hd => by simp only [f, ite_eq_right hd]), sum_mul]
  apply sum_congr rfl
  intro d hd
  simp only [f, ite_eq_left hd, mul_assoc]

/-- A convergent bounded real kernel transfers through an absolutely summable
divisor convolution; the positive summation interval omits the zero coefficient.-/
theorem tendsto_real_divisorConvolution (h : ℕ → ℝ) (B : ℝ → ℝ) (L : ℝ)
    (hh : Summable (fun d => |h d|)) (hhzero : h 0 = 0)
    (hB : Tendsto B atTop (𝓝 L))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x : ℝ, 1 ≤ x → |B x| ≤ C) :
    Tendsto (fun U : ℕ => ∑ d ∈ Ioc 0 U, h d * B ((U : ℝ) / d))
      atTop (𝓝 ((∑' d : ℕ, h d) * L)) := by
  classical
  let f : ℕ → ℕ → ℝ := fun U d =>
    if d ∈ Ioc 0 U then h d * B ((U : ℝ) / d) else 0
  have hpoint (d : ℕ) : Tendsto (fun U => f U d) atTop (𝓝 (h d * L)) := by
    by_cases hd : d = 0
    · subst d
      simp [f, hhzero]
    · have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      have harg : Tendsto (fun U : ℕ => (U : ℝ) / d) atTop atTop :=
        (tendsto_div_const_atTop_of_pos hdR).mpr tendsto_natCast_atTop_atTop
      apply ((hB.comp harg).const_mul (h d)).congr'
      filter_upwards [eventually_ge_atTop d] with U hU
      simp [f, mem_Ioc, Nat.pos_of_ne_zero hd, hU]
  have hdom : ∀ U d, ‖f U d‖ ≤ C * |h d| := by
    intro U d
    by_cases hd : d ∈ Ioc 0 U
    · have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
      have harg : (1 : ℝ) ≤ (U : ℝ) / d :=
        (one_le_div hdR).mpr (by exact_mod_cast (mem_Ioc.mp hd).2)
      simp only [f, ite_eq_left hd, norm_mul, Real.norm_eq_abs]
      nlinarith [mul_le_mul_of_nonneg_left (hbound _ harg) (abs_nonneg (h d))]
    · simp only [f, ite_eq_right hd, norm_zero]
      exact mul_nonneg hC (abs_nonneg (h d))
  have hlim := tendsto_tsum_of_dominated_convergence (hh.mul_left C) hpoint
    (Eventually.of_forall hdom)
  rw [tsum_mul_right] at hlim
  apply hlim.congr'
  filter_upwards with U
  rw [tsum_eq_sum (s := Ioc 0 U) (fun d hd => by simp only [f, ite_eq_right hd])]
  apply sum_congr rfl
  intro d hd
  simp only [f, ite_eq_left hd]

/-- On a finite real interval the finite smoothing sum has an explicit bound.-/
theorem abs_smoothedMoebiusSum_le_on_Icc {x T : ℝ} (hx : 1 ≤ x) (hxT : x ≤ T) :
    |smoothedMoebiusSum x| ≤ (⌊T⌋₊ : ℝ) * Real.log T := by
  have hx0 : 0 < x := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (hx.trans hxT)
  unfold smoothedMoebiusSum
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, |normalizedMoebius n * Real.log (x / n)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log T := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1
      have hnfloor : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (mem_Ioc.mp hn).2
      have hnx : (n : ℝ) ≤ x := hnfloor.trans (Nat.floor_le hx0.le)
      have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
      have hnorm : |normalizedMoebius n| ≤ 1 := by
        rw [normalizedMoebius_apply, abs_div, abs_of_pos hn0]
        exact (div_le_one hn0).mpr (hμ.trans hn1)
      have hlog0 : 0 ≤ Real.log (x / n) := Real.log_nonneg ((one_le_div hn0).mpr hnx)
      have hlogle : Real.log (x / n) ≤ Real.log T := by
        apply Real.log_le_log (div_pos hx0 hn0)
        exact ((div_le_iff₀ hn0).mpr (by nlinarith)).trans hxT
      rw [abs_mul, abs_of_nonneg hlog0]
      calc
        _ ≤ 1 * Real.log T := mul_le_mul hnorm hlogle hlog0 (by norm_num)
        _ = _ := one_mul _
    _ = (⌊x⌋₊ : ℝ) * Real.log T := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.floor_mono hxT) hlogT

/-- Real convergence of the ordinary smoothed sum supplies a uniform bound on
all admissible quotient arguments, without an additional regularity assumption.-/
theorem exists_bound_smoothedMoebiusSum_of_tendsto (L : ℝ)
    (hB : Tendsto smoothedMoebiusSum atTop (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |smoothedMoebiusSum x| ≤ C := by
  have hevent : ∀ᶠ x : ℝ in atTop, |smoothedMoebiusSum x| ≤ |L| + 1 :=
    (hB.abs.eventually (gt_mem_nhds (by linarith : |L| < |L| + 1))).mono (fun _ h => h.le)
  rcases eventually_atTop.mp hevent with ⟨T₀, hT₀⟩
  let T : ℝ := max 1 T₀
  let C : ℝ := max (|L| + 1) ((⌊T⌋₊ : ℝ) * Real.log T)
  refine ⟨C, le_trans (by positivity) (le_max_left _ _), fun x hx => ?_⟩
  by_cases hTx : T ≤ x
  · exact (hT₀ x ((le_max_right _ _).trans hTx)).trans (le_max_left _ _)
  · exact (abs_smoothedMoebiusSum_le_on_Icc hx (le_of_not_ge hTx)).trans (le_max_right _ _)

/-- The ordinary normalized Möbius estimate transfers to the odd totient sum.-/
theorem tendsto_oddMoebiusTotientSum_log_sq_of_normalized
    (hS : Tendsto (fun n : ℕ => normalizedMoebiusSum n * (Real.log (n + 1)) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun U : ℕ => oddMoebiusTotientSum U * (Real.log (U + 1)) ^ 2)
      atTop (𝓝 0) := by
  have h := tendsto_divisorConvolution_mul_log_sq smoothingCorrection normalizedMoebiusSum
    (by simpa only [Real.norm_eq_abs] using summable_norm_smoothingCorrection)
    summable_log_sq_mul_abs_smoothingCorrection hS
  simpa only [← oddMoebiusTotientSum_eq_smoothingConvolution] using h

/-- The smoothed ordinary limit transfers with the independently evaluated
Euler-product mass of the correction coefficients.-/
theorem tendsto_smoothedTotientSum_of_smoothedMoebius
    (hB : Tendsto smoothedMoebiusSum atTop (𝓝 1)) :
    Tendsto smoothedTotientSum atTop (𝓝 (2 * twinPrimeConstant)) := by
  rcases exists_bound_smoothedMoebiusSum_of_tendsto 1 hB with ⟨C, hC, hbound⟩
  have h := tendsto_real_divisorConvolution smoothingCorrection smoothedMoebiusSum 1
    (by simpa only [Real.norm_eq_abs] using summable_norm_smoothingCorrection)
    (by simp) hB C hC hbound
  simpa only [← smoothedTotientSum_eq_smoothingConvolution, tsum_smoothingCorrection, mul_one] using h

end TwinPrime.Analytic
