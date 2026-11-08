module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalized three-term recurrence for `Gegenbauer24`

This file proves the three-term recurrence for the normalized basis `Gegenbauer24`.
In evaluation form (for `n ≥ 0`) it reads:

`t * P_{n+1}(t) = α_n * P_{n+2}(t) + β_n * P_n(t)`,

with `α_n = (n+23)/(2n+24)` and `β_n = (n+1)/(2n+24)`.

## Main statements
* `Gegenbauer24_eval_recurrence_succ`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP
noncomputable section

open Polynomial

private def c (n : ℕ) : ℝ :=
  (gegenbauer gegenbauer24Param n).eval (1 : ℝ)

private lemma c_succ :
    ∀ n : ℕ, c (n + 1) = ((2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ)) * c n := by
  intro n
  simpa [c] using (gegenbauer24_eval_one_succ (n := n))

private lemma c_ne_zero (n : ℕ) : c n ≠ 0 := by
  intro h0
  have hc0 : (gegenbauer gegenbauer24Param n).eval (1 : ℝ) = 0 := by
    simpa [c] using h0
  have hc0' : (gegenbauer (11 : ℝ) n).eval (1 : ℝ) = 0 := by
    simpa [gegenbauer24Param] using hc0
  have hzero : (Gegenbauer24 n).eval (1 : ℝ) = 0 := by
    simp [Gegenbauer24, gegenbauer24Param, hc0']
  have hone : (Gegenbauer24 n).eval (1 : ℝ) = 1 := Gegenbauer24_eval_one n
  have h1 : (1 : ℝ) = 0 := hone.symm.trans hzero
  exact one_ne_zero h1

private lemma gegenbauer_eval_eq_c_mul_Gegenbauer24_eval (n : ℕ) (t : ℝ) :
    (gegenbauer gegenbauer24Param n).eval t = c n * (Gegenbauer24 n).eval t := by
  have hc : c n ≠ 0 := c_ne_zero (n := n)
  -- `Gegenbauer24 n = (C (c n)⁻¹) * gegenbauer gegenbauer24Param n`.
  have h :
      (Gegenbauer24 n).eval t = (c n)⁻¹ * (gegenbauer gegenbauer24Param n).eval t := by
    simp [Gegenbauer24, c, gegenbauer24Param]
  -- Rearrange.
  exact (inv_mul_eq_iff_eq_mul₀ hc).mp (id (Eq.symm h))

private lemma c_ratio_succ (n : ℕ) :
    c (n + 1) / c n = (2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ) := by
  have hc : c n ≠ 0 := c_ne_zero (n := n)
  simp [div_eq_mul_inv, c_succ (n := n), hc, mul_assoc, mul_comm]

private lemma c_ratio_pred (n : ℕ) :
    c n / c (n + 1) = (n + 1 : ℝ) / (2 * gegenbauer24Param + (n : ℝ)) := by
  have hc : c n ≠ 0 := c_ne_zero (n := n)
  have hsucc := c_succ (n := n)
  -- `c (n+1) = ((2*gegenbauer24Param + n)/(n+1)) * c n`, so divide both sides by `c n`.
  -- Then invert.
  -- We keep the algebra in `ℝ`.
  calc
    c n / c (n + 1)
        = c n / (((2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ)) * c n) := by
            simp [hsucc]
    _ = (n + 1 : ℝ) / (2 * gegenbauer24Param + (n : ℝ)) := by
            field_simp [hc]

end

end SpherePacking.Dim24.Uniqueness.BS81.LP
