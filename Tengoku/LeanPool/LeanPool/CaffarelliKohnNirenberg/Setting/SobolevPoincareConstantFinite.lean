/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBall
public import Tengoku

/-!
# Sobolev Poincare Constant Finite

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace CKN

/-- The local Sobolev constant is finite.
@isnad1 id=ne.0h0v.s2.fd90543dc0fb from=translated src=- shape=f463f024 vocab=789ca7af
-/
theorem localSobolevConstant_ne_top : localSobolevConstant ≠ ∞ := by
  unfold localSobolevConstant
  finiteness

/-- The Euclidean ball Poincaré constant is finite.
@isnad1 id=ne.0h0v.s2.68730b38ba85 from=translated src=- shape=f463f024 vocab=79bf582a
-/
theorem euclideanBallPoincareConstant_ne_top : euclideanBallPoincareConstant ≠ ∞ := by
  unfold euclideanBallPoincareConstant
  finiteness

/-- The Sobolev–Poincaré L⁶ constant is finite.
@isnad1 id=ne.0h0v.s2.0a9742768d0d from=translated src=- shape=f463f024 vocab=0a99c5a1
-/
theorem sobolevPoincareL6Constant_ne_top : sobolevPoincareL6Constant ≠ ∞ := by
  unfold sobolevPoincareL6Constant
  refine ENNReal.mul_ne_top ?_ ?_
  · unfold localSobolevConstant
    finiteness
  · have hCg : (let Cg : ℝ≥0∞ :=
      2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) +
      2 * 32 ^ 2 * 6337 * euclideanBallPoincareConstant
    Cg) ≠ ∞ := by
      apply ENNReal.add_ne_top.mpr
      constructor
      · norm_num
      · apply ENNReal.mul_ne_top
        · norm_num
        · exact euclideanBallPoincareConstant_ne_top
    have hpos : (0 : ℝ) ≤ 1/2 := by norm_num
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · apply ENNReal.rpow_ne_top_of_nonneg hpos
      exact hCg
    · refine ENNReal.mul_ne_top (by norm_num) ?_
      refine ENNReal.mul_ne_top ?_ ?_
      · apply ENNReal.rpow_ne_top_of_nonneg hpos
        norm_num
      · apply ENNReal.rpow_ne_top_of_nonneg hpos
        exact euclideanBallPoincareConstant_ne_top

/-- The Sobolev–Poincaré L⁶ constant is less than ∞.
@isnad1 id=lt.0h0v.s3.a4891202daed from=translated src=- shape=f463f024 vocab=8f243703
-/
theorem sobolevPoincareL6Constant_lt_top : sobolevPoincareL6Constant < ∞ := by
  exact lt_top_iff_ne_top.mpr sobolevPoincareL6Constant_ne_top

/-- `sobolevPoincareL6Constant` is real: `ENNReal.ofReal` of its `toReal` equals itself.
@isnad1 id=eq.0h0v.s2.3ca947cb31b2 from=translated src=- shape=fb946a67 vocab=596f901c
-/
theorem ofReal_toReal_sobolevPoincareL6Constant :
    ENNReal.ofReal sobolevPoincareL6Constant.toReal = sobolevPoincareL6Constant := by
  exact ENNReal.ofReal_toReal sobolevPoincareL6Constant_ne_top

end CKN
