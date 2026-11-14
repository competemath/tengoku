import Tengoku.Twinprime.TwinPrime.Analytic.CharacterDirichletTail
import Tengoku.Seed.Analysis.PSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform lower bounds to the right of the critical strip

Separating the coefficient at two and telescoping the remaining inverse
squares gives a uniform lower bound for every Dirichlet L-function on
`2 ≤ s.re`. No zero-free-region or prime-distribution estimate is assumed.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.0h3v.s5.3977e3ccd7fb from=translated src=- shape=0c284d60 vocab=a8cd4dc2
-/
@[simp] theorem characterDirichletPartialSum_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) : characterDirichletPartialSum χ s 1 = 1 := by
  norm_num [characterDirichletPartialSum]

/--
@isnad1 id=le.1h1v.s6.09756baa6893 from=translated src=- shape=efaee915 vocab=ac479230
-/
theorem sum_Ioc_one_inv_sq_le_three_quarters (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Ioc 1 N, ((n : ℝ) ^ 2)⁻¹) ≤ 3 / 4 := by
  have hs := sum_Ioc_consecutive (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)
    (show 1 ≤ 2 by norm_num) hN
  have ht := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 2) (n := N) (by norm_num) hN
  have hi : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  norm_num at hs ht
  linarith

/-- A finite estimate for every character, including principal characters.
@isnad1 id=le.2h4v.s6.cb8a63e8ab0c from=translated src=- shape=e9f68724 vocab=8879730f
-/
theorem norm_characterDirichletPartialSum_sub_one_le {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 2 ≤ s.re)
    (N : ℕ) (hN : 2 ≤ N) :
    ‖characterDirichletPartialSum χ s N - 1‖ ≤ 3 / 4 := by
  rw [← characterDirichletPartialSum_one χ s,
    characterDirichletPartialSum_sub χ s (by omega)]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum fun n hn => ?_).trans (sum_Ioc_one_inv_sq_le_three_quarters N hN)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by have := mem_Ioc.mp hn; omega)
  have hpow : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
    simpa only [Complex.ofReal_natCast, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos (y := -s) (by linarith : (0 : ℝ) < n)
  rw [norm_mul, hpow]
  calc
    _ ≤ (n : ℝ) ^ (-s.re) * 1 :=
      mul_le_mul_of_nonneg_left (χ.norm_le_one _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (n : ℝ) ^ (-s.re) := mul_one _
    _ ≤ (n : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ = _ := by rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two]

/--
@isnad1 id=le.1h3v.s6.fccbfb8c6a30 from=translated src=- shape=de3cb080 vocab=68389610
-/
theorem norm_LFunction_sub_one_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s - 1‖ ≤ 3 / 4 := by
  have hL := tendsto_characterDirichletPartialSum_LFunction χ s (by linarith)
  apply le_of_tendsto ((hL.sub tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact norm_characterDirichletPartialSum_sub_one_le χ s hs N hN

/-- An absolute center-value lower bound suitable for local zero estimates.
@isnad1 id=le.1h3v.s6.a47d890a8d1c from=translated src=- shape=21a2f84d vocab=7f263296
-/
theorem one_quarter_le_norm_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 2 ≤ s.re) :
    1 / 4 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have h := norm_LFunction_sub_one_le χ s hs
  have htriangle : (1 : ℝ) ≤
      ‖DirichletCharacter.LFunction χ s - 1‖ + ‖DirichletCharacter.LFunction χ s‖ := by
    calc
      _ = ‖(1 - DirichletCharacter.LFunction χ s) + DirichletCharacter.LFunction χ s‖ := by simp
      _ ≤ _ := by simpa only [norm_sub_rev] using
        norm_add_le (1 - DirichletCharacter.LFunction χ s) (DirichletCharacter.LFunction χ s)
  linarith

/--
@isnad1 id=le.1h3v.s5.b6a6cadd0c4e from=translated src=- shape=a1a18f72 vocab=1d2666cd
-/
theorem norm_inv_LFunction_le_four {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ 4 := by
  rw [norm_inv]
  have h := one_quarter_le_norm_LFunction χ s hs
  calc
    _ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
    _ = _ := by norm_num

end TwinPrime.Analytic
