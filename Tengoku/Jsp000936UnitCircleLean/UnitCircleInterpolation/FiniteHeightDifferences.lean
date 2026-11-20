/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Seed.Analysis.Normed.Group.Constructions
import Tengoku.Seed.Analysis.Normed.Group.Real
import Tengoku.Seed.Data.Fin.Basic
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite height differences control every height oscillation

The norm on the finite difference vector is the ordinary sup norm. Finite
induction bounds each height relative to the first, and the triangle inequality
bounds every pair. The zero-dimensional case is part of the same statements.
These bounds do not assert properness of any nonlinear map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

def finiteHeightDifferences (H : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun k => H k.succ - H k.castSucc

/--
@isnad1 id=eq.0h3v.s5.5ce1d66a4a51 from=translated src=- shape=7ea9eb51 vocab=bddea338
-/
@[simp] lemma finiteHeightDifferences_apply (H : Fin (d + 1) → ℝ) (k : Fin d) :
    finiteHeightDifferences H k = H k.succ - H k.castSucc := rfl

/-- Each consecutive height difference is bounded by the literal finite sup norm.
@isnad1 id=le.0h3v.s6.a9d755e8a802 from=translated src=- shape=22d15ecc vocab=709db0c7
-/
lemma abs_adjacent_height_sub_le_norm (H : Fin (d + 1) → ℝ) (k : Fin d) :
    |H k.succ - H k.castSucc| ≤ ‖finiteHeightDifferences H‖ := by
  simpa only [Real.norm_eq_abs, finiteHeightDifferences_apply] using
    norm_le_pi_norm (finiteHeightDifferences H) k

/-- Finite induction accumulates at most one difference norm per preceding index.
@isnad1 id=le.0h3v.s7.25d6e8107289 from=translated src=- shape=2eed422f vocab=39d7b33e
-/
lemma abs_height_sub_first_le_index_mul_norm (H : Fin (d + 1) → ℝ)
    (i : Fin (d + 1)) :
    |H i - H 0| ≤ (i.val : ℝ) * ‖finiteHeightDifferences H‖ := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    calc
      |H i.succ - H 0| = |(H i.succ - H i.castSucc) + (H i.castSucc - H 0)| := by
        congr 1
        ring
      _ ≤ |H i.succ - H i.castSucc| + |H i.castSucc - H 0| := abs_add_le _ _
      _ ≤ ‖finiteHeightDifferences H‖ + (i.val : ℝ) * ‖finiteHeightDifferences H‖ :=
        add_le_add (abs_adjacent_height_sub_le_norm H i) ih
      _ = (i.succ.val : ℝ) * ‖finiteHeightDifferences H‖ := by
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        ring

/-- The finite difference norm controls every literal height difference uniformly.
@isnad1 id=le.0h4v.s6.40021d2c3b9a from=translated src=- shape=02e9345b vocab=3a3a64c7
-/
lemma abs_height_sub_le_two_dim_mul_norm (H : Fin (d + 1) → ℝ)
    (i j : Fin (d + 1)) :
    |H i - H j| ≤ 2 * (d : ℝ) * ‖finiteHeightDifferences H‖ := by
  have hi : (i.val : ℝ) ≤ (d : ℝ) := by
    exact Nat.cast_le.mpr (show i.val ≤ d by omega)
  have hj : (j.val : ℝ) ≤ (d : ℝ) := by
    exact Nat.cast_le.mpr (show j.val ≤ d by omega)
  calc
    |H i - H j| = |(H i - H 0) - (H j - H 0)| := by
      congr 1
      ring
    _ ≤ |H i - H 0| + |H j - H 0| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (H i - H 0) (H j - H 0)
    _ ≤ (i.val : ℝ) * ‖finiteHeightDifferences H‖ +
        (j.val : ℝ) * ‖finiteHeightDifferences H‖ :=
      add_le_add (abs_height_sub_first_le_index_mul_norm H i)
        (abs_height_sub_first_le_index_mul_norm H j)
    _ ≤ (d : ℝ) * ‖finiteHeightDifferences H‖ + (d : ℝ) * ‖finiteHeightDifferences H‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hj (norm_nonneg _))
    _ = 2 * (d : ℝ) * ‖finiteHeightDifferences H‖ := by ring

/--
@isnad1 id=le.0h4v.s6.ae105a2f04fb from=translated src=- shape=6464c527 vocab=9772e391
-/
lemma height_sub_le_two_dim_mul_norm (H : Fin (d + 1) → ℝ)
    (i j : Fin (d + 1)) :
    H i - H j ≤ 2 * (d : ℝ) * ‖finiteHeightDifferences H‖ :=
  (le_abs_self _).trans (abs_height_sub_le_two_dim_mul_norm H i j)

/-- A vanishing finite difference vector means all heights are the first height.
@isnad1 id=iff.0h2v.s6.7a040c7915f3 from=translated src=- shape=a8ffa789 vocab=960d2682
-/
lemma finiteHeightDifferences_eq_zero_iff (H : Fin (d + 1) → ℝ) :
    finiteHeightDifferences H = 0 ↔ ∀ i, H i = H 0 := by
  constructor
  · intro hzero i
    have h := abs_height_sub_first_le_index_mul_norm H i
    rw [hzero, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  · intro hconst
    funext k
    simp only [finiteHeightDifferences_apply, hconst k.succ, hconst k.castSucc,
      sub_self, Pi.zero_apply]

end

end UnitCircleInterpolation
