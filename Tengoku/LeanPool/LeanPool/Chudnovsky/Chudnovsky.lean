/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.Chudnovsky.Basic
import Tengoku.LeanPool.LeanPool.Chudnovsky.Coefficients
import Tengoku.LeanPool.LeanPool.Chudnovsky.MainTheorem

/-!
# Glue: from Milla's `theohud` to Mathlib's `chudnovskySum = π⁻¹`

Phase D3 of the PLAN: convert Milla's normalization
`√(640320³)/(12π) = ∑ n, (6n)!/((3n)!(n!)³)·(13591409 + 545140134·n)/(−640320³)ⁿ`
into Mathlib's statement `chudnovskySum = π⁻¹`, where
`chudnovskySum = 12/640320^(3/2) · ∑' n, chudnovskyTerm n`. This involves
`640320^(3/2 : ℝ) = √(640320³)` (rpow lemmas), the `ℚ → ℝ` coercion of
`chudnovskyTerm`, and inverting both (positive) sides.

The intermediate milestone `chudnovsky_of_singular_moduli` states the full theorem with
the Phase C inputs (`SingularModuli.lean`) as explicit hypotheses: the paper's proof
minus the literature citations (Silverman II.6.1, II.4.3(b), Buell, Masser Thm. A1).
-/

@[expose] public section

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex Nat

open scoped Real

/-- The factorial bound from the Main Theorem controls the series normalization. -/
private theorem factorial_six_bound (n : ℕ) :
    (6 * n)! ≤ 1728 ^ n * ((3 * n)! * (n ! ) ^ 3) :=
  factorial_ratio_le n

/-- The Chudnovsky series is (absolutely) summable — needed for `hauptformel`
substitution, the series rearrangement, and the final inversion. -/
theorem summable_chudnovskyTerm : Summable fun n : ℕ ↦ (chudnovskyTerm n : ℝ) := by
  -- Comparison against `(545140134·n + 13591409)·rⁿ` with `r = 1728/640320³ < 1`.
  set r : ℝ := 1728 / 640320 ^ 3 with hr_def
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; rw [hr_def]; norm_num
  have hg1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hg0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr
  have hg : Summable (fun n : ℕ => (545140134 * (n : ℝ) + 13591409) * r ^ n) := by
    have hrw : (fun n : ℕ => (545140134 * (n : ℝ) + 13591409) * r ^ n)
        = (fun n : ℕ => 545140134 * ((n : ℝ) * r ^ n) + 13591409 * r ^ n) := by
      funext n; ring
    rw [hrw]
    exact (hg1.mul_left 545140134).add (hg0.mul_left 13591409)
  refine hg.of_norm_bounded (fun n => ?_)
  -- `|chudnovskyTerm n| = (6n)!·(545140134n+13591409)/((3n)!(n!)³·640320^{3n})`.
  have hval : (chudnovskyTerm n : ℝ)
      = (-1:ℝ)^n * ((((6*n)! : ℝ) * (545140134*n+13591409))
          / (((3*n)! : ℝ) * (n ! )^3 * 640320^(3*n))) := by
    simp only [chudnovskyTerm, chudnovskyNum, chudnovskyDenom]
    push_cast
    ring
  rw [Real.norm_eq_abs, hval, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity)]
  -- Reduce to `(6n)! ≤ 1728ⁿ·(3n)!·(n!)³`.
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ((3*n)! : ℝ) * (n ! )^3 * 640320^(3*n))]
  have key : ((6*n)! : ℝ) ≤ 1728^n * (((3*n)! : ℝ) * (n ! )^3) := by
    have h := factorial_six_bound n
    calc ((6*n)! : ℝ) ≤ ((1728^n * ((3*n)! * (n ! )^3) : ℕ) : ℝ) := by exact_mod_cast h
      _ = 1728^n * (((3*n)! : ℝ) * (n ! )^3) := by push_cast; ring
  have hApos : (0:ℝ) ≤ 545140134*(n:ℝ)+13591409 := by positivity
  have hrpow : r^n * (640320:ℝ)^(3*n) = 1728^n := by
    rw [hr_def, div_pow, ← pow_mul,
      div_mul_cancel₀ _ (by positivity : (640320:ℝ)^(3*n) ≠ 0)]
  rw [show (545140134 * (n:ℝ) + 13591409) * r ^ n
        * (((3*n)! : ℝ) * (n ! )^3 * 640320^(3*n))
      = (545140134 * (n:ℝ) + 13591409) * (r ^ n * 640320^(3*n))
          * (((3*n)! : ℝ) * (n ! )^3) from by ring, hrpow]
  linear_combination mul_le_mul_of_nonneg_left key hApos

end Chudnovsky
