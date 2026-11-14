import Tengoku.Twinprime.TwinPrime.Analytic.CharacterDirichletContinuation
import Tengoku.Twinprime.TwinPrime.Analytic.BVLogComparisons
import Tengoku.Seed.Analysis.Complex.Liouville
import Tengoku.Seed.NumberTheory.Harmonic.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Primitive L-function bounds in a logarithmic neighborhood of one

The actual truncation estimate at `M = q` gives logarithmic growth in a
disk of radius `1 / log q`. Cauchy's estimate then gives a logarithmic-square
derivative bound, without an exceptional-zero or distribution assumption.
-/

noncomputable section

open Finset Metric

namespace TwinPrime.Analytic

/--
@isnad1 id=le.4h3v.s6.256a08cd12d9 from=translated src=- shape=34572276 vocab=1d2dc258
-/
theorem rpow_neg_le_exp_two_div_of_near_one {q n : ℕ}
    (hq : 1 < q) (hn : 1 ≤ n) (hnq : n ≤ q) (σ : ℝ)
    (hσ : 1 - 2 / Real.log q ≤ σ) :
    (n : ℝ) ^ (-σ) ≤ Real.exp 2 / n := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlognq : Real.log (n : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hn0 (by exact_mod_cast hnq)
  have hprod : Real.log (n : ℝ) * (1 - σ) ≤ 2 := by
    calc
      _ ≤ Real.log (n : ℝ) * (2 / Real.log q) :=
        mul_le_mul_of_nonneg_left (by linarith) hlogn
      _ ≤ Real.log (q : ℝ) * (2 / Real.log q) :=
        mul_le_mul_of_nonneg_right hlognq (by positivity)
      _ = 2 := by field_simp
  calc
    _ = Real.exp (Real.log (n : ℝ) * (-σ)) := Real.rpow_def_of_pos hn0 _
    _ ≤ Real.exp (2 - Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log hn0]

/-- The finite sum at the conductor is bounded by the harmonic sum.
@isnad1 id=le.2h3v.s6.fdfb6115a68a from=translated src=- shape=6710d637 vocab=3edc51f2
-/
theorem norm_characterDirichletPartialSum_conductor_le_near_one {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hσ : 1 - 2 / Real.log q ≤ s.re) :
    ‖characterDirichletPartialSum χ s q‖ ≤ Real.exp 2 * (1 + Real.log q) := by
  have hsum : ‖characterDirichletPartialSum χ s q‖ ≤
      ∑ n ∈ Ioc 0 q, Real.exp 2 / (n : ℝ) := by
    unfold characterDirichletPartialSum
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
    apply (mul_le_of_le_one_right (Real.rpow_nonneg hn0.le _) (χ.norm_le_one _)).trans
    exact rpow_neg_le_exp_two_div_of_near_one hq
      (Nat.succ_le_of_lt (mem_Ioc.mp hn).1) (mem_Ioc.mp hn).2 s.re hσ
  apply hsum.trans
  have hI : Ioc 0 q = Icc 1 q := by ext n; simp; omega
  rw [hI]
  simp_rw [div_eq_mul_inv]
  rw [← mul_sum]
  have hh : (∑ n ∈ Icc 1 q, (n : ℝ)⁻¹) ≤ 1 + Real.log q := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log q
  exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

/-- Actual primitive L-function growth from truncation at its conductor.
@isnad1 id=le.4h3v.s7.adf17cece8ab from=translated src=- shape=262826c4 vocab=2ec764b2
-/
theorem norm_LFunction_le_near_one {q : ℕ} [NeZero q]
    (hq : 256 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (hσ : 1 - 2 / Real.log q ≤ s.re) (hs : ‖s‖ ≤ 5 / 4) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 10 * Real.exp 2 * Real.log q := by
  have hq1 : 1 < q := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hq0 : (0 : ℝ) < q := by positivity
  have hlog : 4 ≤ Real.log (q : ℝ) := by
    linarith [eight_log_two_le_log_nat q hq, half_le_log_two]
  have hlog0 : 0 < Real.log (q : ℝ) := by linarith
  have hfrac : 2 / Real.log (q : ℝ) ≤ 1 / 2 :=
    (div_le_iff₀ hlog0).mpr (by linarith)
  have hσhalf : (1 / 2 : ℝ) ≤ s.re := by linarith
  have hσ0 : 0 < s.re := by linarith
  have hratio : 1 + ‖s‖ / s.re ≤ 4 := by
    have : ‖s‖ / s.re ≤ 5 / 2 := (div_le_iff₀ hσ0).mpr (by nlinarith)
    linarith
  have hpow := rpow_neg_le_exp_two_div_of_near_one hq1
    (show 1 ≤ q by omega) le_rfl s.re hσ
  have hsqrt : Real.sqrt (q : ℝ) ≤ q := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hq0.le, by nlinarith⟩
  have hp : Real.sqrt (q : ℝ) * (q : ℝ) ^ (-s.re) ≤ Real.exp 2 := by
    calc
      _ ≤ Real.sqrt (q : ℝ) * (Real.exp 2 / q) :=
        mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
      _ ≤ (q : ℝ) * (Real.exp 2 / q) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ = _ := by field_simp
  have ht := norm_LFunction_sub_characterDirichletPartialSum_le_of_re_pos
    hq1 χ hχ q (by omega) s hσ0
  have ht' : ‖DirichletCharacter.LFunction χ s - characterDirichletPartialSum χ s q‖ ≤
      4 * Real.exp 2 * (1 + Real.log q) := by
    apply ht.trans
    calc
      _ = (Real.sqrt (q : ℝ) * (q : ℝ) ^ (-s.re)) * (1 + Real.log q) *
          (1 + ‖s‖ / s.re) := by ring
      _ ≤ Real.exp 2 * (1 + Real.log q) * 4 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hp (by linarith)
        · exact hratio
        · positivity
        · positivity
      _ = _ := by ring
  have hf := norm_characterDirichletPartialSum_conductor_le_near_one hq1 χ s hσ
  have hadd := norm_add_le
    (DirichletCharacter.LFunction χ s - characterDirichletPartialSum χ s q)
    (characterDirichletPartialSum χ s q)
  rw [sub_add_cancel] at hadd
  have he : 0 < Real.exp 2 := Real.exp_pos _
  nlinarith

/-- The logarithmic-radius disk fits the strip used by the conductor truncation.
@isnad1 id=le.5h4v.s7.6fcc53ad4c1b from=translated src=- shape=0b89b901 vocab=45f04293
-/
theorem norm_LFunction_le_on_near_one_closedBall {q : ℕ} [NeZero q]
    (hq : 256 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (u : ℝ) (hu : 1 - 1 / Real.log q ≤ u) (hu1 : u ≤ 1)
    (s : ℂ) (hs : s ∈ closedBall (u : ℂ) (1 / Real.log q)) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 10 * Real.exp 2 * Real.log q := by
  have hlog : 4 ≤ Real.log (q : ℝ) := by
    linarith [eight_log_two_le_log_nat q hq, half_le_log_two]
  have hlog0 : 0 < Real.log (q : ℝ) := by linarith
  have hr : 1 / Real.log (q : ℝ) ≤ 1 / 4 :=
    (div_le_iff₀ hlog0).mpr (by linarith)
  have hu0 : 0 ≤ u := by linarith
  have hdist := mem_closedBall_iff_norm.mp hs
  have hre := (abs_le.mp (Complex.abs_re_le_norm (s - (u : ℂ)))).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  apply norm_LFunction_le_near_one hq χ hχ s
  · have htwo : 2 / Real.log (q : ℝ) = 2 * (1 / Real.log q) := by ring
    rw [htwo]
    linarith
  · have hn := norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hs)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at hn
    linarith

/-- A Cauchy estimate with only a logarithmic-square conductor cost near one.
@isnad1 id=le.4h3v.s7.cc2ed8a09576 from=translated src=- shape=34b5372a vocab=6d2b71dc
-/
theorem norm_deriv_LFunction_near_one_le {q : ℕ} [NeZero q]
    (hq : 256 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (u : ℝ) (hu : 1 - 1 / Real.log q ≤ u) (hu1 : u ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction χ) (u : ℂ)‖ ≤
      10 * Real.exp 2 * (Real.log q) ^ 2 := by
  have hlog0 : 0 < Real.log (q : ℝ) := by
    linarith [one_le_log_of_256_le q hq]
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (one_div_pos.mpr hlog0)
    (DirichletCharacter.differentiable_LFunction
      (primitive_character_ne_one (by omega) χ hχ)).diffContOnCl
    (fun s hs => norm_LFunction_le_on_near_one_closedBall hq χ hχ u hu hu1 s
      (sphere_subset_closedBall hs))
  apply hC.trans_eq
  field_simp

end TwinPrime.Analytic
