import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionNonquadraticZeroFree
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionConjugateZeros

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniqueness and simplicity of a zero very near one

At a real evaluation point just to the right of one, the actual zero sum
has an upper bound `5 E`. Each zero in the specified rectangle contributes
at least `3 E`, with its actual multiplicity. Thus there is at most one
such zero and its multiplicity is one. For a real character conjugation
then forces the zero to be real. This does not bound its distance from one
by a Siegel-type power of the conductor.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

def nearOneZeroBudget (q : ℕ) : ℝ := 40 + primitiveLFunctionLogBudget q 0

def nearOneEvaluationShift (q : ℕ) : ℝ := 1 / (4 * nearOneZeroBudget q)

def nearOneZeroWidth (q : ℕ) : ℝ := 1 / (16 * nearOneZeroBudget q)

/--
@isnad1 id=le.0h1v.s3.ee734e159c58 from=translated src=- shape=b9369acb vocab=84a86b6b
-/
theorem nearOneZeroBudget_ge (q : ℕ) : 40 ≤ nearOneZeroBudget q := by
  have h := primitiveLFunctionLogBudget_nonneg q 0
  unfold nearOneZeroBudget
  linarith

/--
@isnad1 id=lt.0h1v.s3.6ca94cd075b8 from=translated src=- shape=b9369acb vocab=8c71aa03
-/
theorem nearOneZeroBudget_pos (q : ℕ) : 0 < nearOneZeroBudget q := by
  have h := nearOneZeroBudget_ge q
  linarith

/--
@isnad1 id=lt.0h1v.s3.a178c77447dc from=translated src=- shape=b9369acb vocab=48441877
-/
theorem nearOneEvaluationShift_pos (q : ℕ) : 0 < nearOneEvaluationShift q := by
  unfold nearOneEvaluationShift
  exact one_div_pos.mpr (mul_pos (by norm_num) (nearOneZeroBudget_pos q))

/--
@isnad1 id=le.0h1v.s4.4952b27e1a62 from=translated src=- shape=23a617a7 vocab=f9ccff56
-/
theorem nearOneEvaluationShift_le_one_eighth (q : ℕ) : nearOneEvaluationShift q ≤ 1 / 8 := by
  have h := nearOneZeroBudget_ge q
  unfold nearOneEvaluationShift
  apply (div_le_iff₀ (by linarith : 0 < 4 * nearOneZeroBudget q)).mpr
  linarith

/--
@isnad1 id=eq.0h1v.s4.be087e0bf515 from=translated src=- shape=cd2b45a8 vocab=3106cf45
-/
theorem nearOneZeroWidth_eq_shift_div_four (q : ℕ) :
    nearOneZeroWidth q = nearOneEvaluationShift q / 4 := by
  unfold nearOneZeroWidth nearOneEvaluationShift
  ring

/--
@isnad1 id=lt.0h1v.s3.037bef68b806 from=translated src=- shape=b9369acb vocab=260bbae2
-/
theorem nearOneZeroWidth_pos (q : ℕ) : 0 < nearOneZeroWidth q := by
  rw [nearOneZeroWidth_eq_shift_div_four]
  exact div_pos (nearOneEvaluationShift_pos q) (by norm_num)

/--
@isnad1 id=le.0h1v.s4.f6ebb5b67152 from=translated src=- shape=23a617a7 vocab=42021d4d
-/
theorem nearOneZeroWidth_le_one_eighth (q : ℕ) : nearOneZeroWidth q ≤ 1 / 8 := by
  rw [nearOneZeroWidth_eq_shift_div_four]
  have h := nearOneEvaluationShift_le_one_eighth q
  linarith

/-- The reciprocal kernel has a uniform lower bound in the small rectangle.
@isnad1 id=le.4h3v.s7.2116715f23b3 from=translated src=- shape=31bb2675 vocab=b09e3a18
-/
theorem nearOne_reciprocal_kernel_lower {a δ t : ℝ} (ha : 0 < a)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ a / 4) (ht : |t| ≤ a / 4) :
    3 / (4 * a) ≤ (a + δ) / ((a + δ) ^ 2 + t ^ 2) := by
  have had : a * δ ≤ a ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_left hδ ha.le
    nlinarith
  have hd2 : δ ^ 2 ≤ a ^ 2 / 16 := by
    have h := mul_nonneg hδ0 (sub_nonneg.mpr hδ)
    nlinarith
  have ht2 : t ^ 2 ≤ a ^ 2 / 16 := by
    have htl := (abs_le.mp ht).1
    have htu := (abs_le.mp ht).2
    have h := mul_nonneg (by linarith : 0 ≤ a / 4 - t) (by linarith : 0 ≤ a / 4 + t)
    nlinarith
  have hden : 0 < (a + δ) ^ 2 + t ^ 2 := by
    nlinarith [sq_nonneg t, sq_pos_of_pos (by linarith : 0 < a + δ)]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * a) hden).mpr
  nlinarith

/--
@isnad1 id=mem.5h3v.s7.d625c29d9460 from=translated src=- shape=3150a642 vocab=97ce17e5
-/
theorem nearOne_zero_mem_local_disk {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ρ : ℂ)
    (hβ : 1 - nearOneZeroWidth q ≤ ρ.re) (ht : |ρ.im| ≤ nearOneZeroWidth q)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ρ ∈ closedBall (2 : ℂ) (5 / 4) := by
  have hβ1 := primitiveLFunction_zero_re_lt_one hq χ hχ ρ hzero
  have heps := nearOneZeroWidth_le_one_eighth q
  have hn := Complex.norm_le_abs_re_add_abs_im (ρ - 2)
  norm_num [abs_of_nonpos (by linarith : ρ.re - 2 ≤ 0)] at hn
  rw [mem_closedBall_iff_norm]
  linarith

/--
@isnad1 id=le.5h3v.s7.dda7bd272160 from=translated src=- shape=2b36e5ee vocab=b8f9fc32
-/
theorem nearOne_zero_reciprocal_re_ge_three_budget {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ρ : ℂ)
    (hβ : 1 - nearOneZeroWidth q ≤ ρ.re) (ht : |ρ.im| ≤ nearOneZeroWidth q)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    3 * nearOneZeroBudget q ≤
      (1 / (((1 + nearOneEvaluationShift q : ℝ) : ℂ) - ρ)).re := by
  have hβ1 := primitiveLFunction_zero_re_lt_one hq χ hχ ρ hzero
  have hδ : 1 - ρ.re ≤ nearOneEvaluationShift q / 4 := by
    rw [← nearOneZeroWidth_eq_shift_div_four]
    linarith
  have htl : |ρ.im| ≤ nearOneEvaluationShift q / 4 := by
    rwa [← nearOneZeroWidth_eq_shift_div_four]
  have hb := nearOne_reciprocal_kernel_lower (nearOneEvaluationShift_pos q)
    (by linarith : 0 ≤ 1 - ρ.re) hδ htl
  have hrepr : ρ = (ρ.re : ℂ) + Complex.I * ρ.im := by
    simpa only [mul_comm] using (Complex.re_add_im ρ).symm
  have he : (1 / (((1 + nearOneEvaluationShift q : ℝ) : ℂ) - ρ)).re =
      (nearOneEvaluationShift q + (1 - ρ.re)) /
        ((nearOneEvaluationShift q + (1 - ρ.re)) ^ 2 + ρ.im ^ 2) := by
    conv_lhs => rw [hrepr, re_one_div_real_sub_complex]
    ring
  rw [he]
  have hscale : 3 / (4 * nearOneEvaluationShift q) = 3 * nearOneZeroBudget q := by
    unfold nearOneEvaluationShift
    field_simp
  rwa [hscale] at hb

end TwinPrime.Analytic
