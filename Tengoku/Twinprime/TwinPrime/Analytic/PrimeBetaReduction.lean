import Tengoku.Twinprime.TwinPrime.Analytic.BilinearPrimeBeta
import Tengoku.Twinprime.TwinPrime.Analytic.NonprimeMangoldtTail
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeBetaGrowth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform error in the prime-divisor beta replacement

The reciprocal proper-prime-power tail bounds the absolute error on the
original factor domain. The constant is independent of both cutoffs and X.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/--
@isnad1 id=ex.0h0v.s7.0d3dd492228d from=translated src=- shape=1dab4a3d vocab=7253991a
-/
theorem exists_bilinearPrimeBetaErrorMass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ U V X : ℕ, 1 ≤ V → 1 ≤ X →
      bilinearPrimeBetaErrorMass U V X ≤
        C * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 * (V : ℝ) ^ (-1 / 2 : ℝ) := by
  obtain ⟨K, hK, htail⟩ := exists_nonprimeMangoldt_reciprocal_tail_bound
  refine ⟨4 * K, by positivity, ?_⟩
  intro U V X hV hX
  calc
    _ ≤ 4 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 *
        ∑ b ∈ Finset.Ioc V (2 * X), nonprimeMangoldt b / b :=
      bilinearPrimeBetaErrorMass_le_tail U V X hX
    _ ≤ 4 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 *
        (K * (V : ℝ) ^ (-1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (htail V hV (2 * X)) (by positivity)
    _ = _ := by ring

/--
@isnad1 id=ex.0h0v.s7.ff7bc5e70ea1 from=translated src=- shape=5230f001 vocab=3bf6a533
-/
theorem exists_abs_bilinear_sub_primeBeta_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ U V X : ℕ, 1 ≤ V → 1 ≤ X →
      |bilinearTerm U V X - bilinearPrimeBeta U V X| ≤
        C * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 * (V : ℝ) ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_bilinearPrimeBetaErrorMass_bound
  exact ⟨C, hC, fun U V X hV hX =>
    (abs_bilinear_sub_primeBeta_le_mass U V X).trans (hbound U V X hV hX)⟩

/--
@isnad1 id=tendsto.0h2v.s6.e261f0213be7 from=translated src=- shape=8b14a4a1 vocab=92b07e1c
-/
theorem tendsto_bilinearPrimeBetaErrorMass_div_mul_log_pow (U : ℕ → ℕ) (k : ℕ) :
    Tendsto (fun X : ℕ =>
      bilinearPrimeBetaErrorMass (U X) (primaryCutoff X) X / X *
        (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  obtain ⟨C, _, hbound⟩ := exists_bilinearPrimeBetaErrorMass_bound
  apply tendsto_mul_dispersion_log_pow_of_primaryCutoff_neg_half_bound _ C 2 k
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  rw [abs_of_nonneg (div_nonneg (bilinearPrimeBetaErrorMass_nonneg _ _ _) hx.le)]
  calc
    _ ≤ (C * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 *
        (primaryCutoff X : ℝ) ^ (-1 / 2 : ℝ)) / X :=
      div_le_div_of_nonneg_right (hbound (U X) (primaryCutoff X) X
        (primaryCutoff_pos hX) hX) hx.le
    _ = _ := by field_simp

/--
@isnad1 id=tendsto.0h1v.s5.33f1df57609c from=translated src=- shape=6bdc9954 vocab=647a55c4
-/
theorem tendsto_bilinearPrimeBetaErrorMass_div (U : ℕ → ℕ) :
    Tendsto (fun X : ℕ => bilinearPrimeBetaErrorMass (U X) (primaryCutoff X) X / X)
      atTop (nhds 0) := by
  simpa using tendsto_bilinearPrimeBetaErrorMass_div_mul_log_pow U 0

/--
@isnad1 id=tendsto.0h2v.s6.20a4c913bd7b from=translated src=- shape=4b4f2c36 vocab=eef8c2a2
-/
theorem tendsto_bilinear_sub_primeBeta_div_mul_log_pow (U : ℕ → ℕ) (k : ℕ) :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (U X) (primaryCutoff X) X - bilinearPrimeBeta (U X) (primaryCutoff X) X) /
        X * (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  obtain ⟨C, _, hbound⟩ := exists_abs_bilinear_sub_primeBeta_bound
  apply tendsto_mul_dispersion_log_pow_of_primaryCutoff_neg_half_bound _ C 2 k
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  rw [abs_div, abs_of_nonneg hx.le]
  calc
    _ ≤ (C * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 *
        (primaryCutoff X : ℝ) ^ (-1 / 2 : ℝ)) / X :=
      div_le_div_of_nonneg_right (hbound (U X) (primaryCutoff X) X
        (primaryCutoff_pos hX) hX) hx.le
    _ = _ := by field_simp

/--
@isnad1 id=tendsto.0h1v.s5.2ddca5c441e5 from=translated src=- shape=d309da66 vocab=456e5c21
-/
theorem tendsto_bilinear_sub_primeBeta_div (U : ℕ → ℕ) :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (U X) (primaryCutoff X) X - bilinearPrimeBeta (U X) (primaryCutoff X) X) / X)
      atTop (nhds 0) := by
  simpa using tendsto_bilinear_sub_primeBeta_div_mul_log_pow U 0

end TwinPrime.Analytic
