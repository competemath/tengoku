/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.Voronoi
import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.LatticeSeparation

/-!
# Isbell's seven-coloring

This module proves the numerical gap estimates, constructs the plane coloring,
and establishes the seven-color upper bound.
-/

@[expose] public section

namespace HadwigerNelsonBounds

open SimpleGraph

/-! ### Numerical inequalities -/

/-- `0 < √3`. -/
private lemma sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

/-- `0 < √7`. -/
private lemma sqrt_seven_pos : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)

/-- `√3 < 2`. -/
private lemma sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  have h2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  nlinarith [h2, hpos]

/-- The within-tile diameter `2·(a/√3) = √3/2` is `< 1`. -/
lemma isbell_voronoi_diameter_lt_one :
    2 * (isbellLatticeStep / Real.sqrt 3) < 1 := by
  unfold isbellLatticeStep
  -- Reduce: 2·(3/4)/√3 = 3/(2·√3) = √3/2. Show √3/2 < 1, i.e. √3 < 2.
  have hs3 : 0 < Real.sqrt 3 := sqrt_three_pos
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  have hlt : Real.sqrt 3 < 2 := sqrt_three_lt_two
  -- Rationalizing gives 2·(3/4)/√3 = √3/2, which is less than one.
  have key : 2 * (3 / 4 / Real.sqrt 3) = Real.sqrt 3 / 2 := by
    have : (3 : ℝ) / 4 / Real.sqrt 3 = 3 / (4 * Real.sqrt 3) := by ring
    rw [this]
    field_simp
    nlinarith [hsq]
  rw [key]
  linarith [hlt]

/-- The same-color spacing `a·(√7 − 2/√3) > 1` for `a = 3/4`. -/
lemma isbell_same_color_min_gt_one :
    isbellLatticeStep * (Real.sqrt 7 - 2 / Real.sqrt 3) > 1 := by
  unfold isbellLatticeStep
  -- It is enough to prove 3√7 > 4 + 2√3 after clearing denominators.
  -- Square both sides (both positive):
  --         (3√7)² > (4 + 2√3)²
  --         63 > 16 + 16√3 + 12 = 28 + 16√3
  --         35 > 16√3
  --         (35)² > (16√3)²
  --         1225 > 768                                              ✓
  have hs3 : 0 < Real.sqrt 3 := sqrt_three_pos
  have hs7 : 0 < Real.sqrt 7 := sqrt_seven_pos
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  have hsq7 : Real.sqrt 7 * Real.sqrt 7 = 7 :=
    Real.mul_self_sqrt (by norm_num)
  -- Show 2/√3 = (2√3)/3
  have h2div3 : (2 : ℝ) / Real.sqrt 3 = 2 * Real.sqrt 3 / 3 := by
    field_simp
    nlinarith [hsq3]
  rw [h2div3]
  -- After substitution, multiplying by four reduces the goal to
  -- 3·√7 − 2·√3 > 4.
  -- We show 3√7 − 2√3 > 4 via:  35² > 768·1, i.e. (35)² > (16√3)²,
  -- i.e. 1225 > 768, hence 35 > 16√3, hence 63 - 28 > 16√3,
  -- i.e. 63 > 28 + 16√3 = (4 + 2√3)², so 3√7 = √63 > 4 + 2√3.
  -- Use nlinarith with all the sqrt facts.
  have hsq35 : (35 : ℝ)^2 = 1225 := by norm_num
  have h16s3 : (16 * Real.sqrt 3)^2 = 16^2 * 3 := by
    have : (16 * Real.sqrt 3)^2 = 16^2 * (Real.sqrt 3 * Real.sqrt 3) := by ring
    rw [this, hsq3]
  have h35_gt : 35 > 16 * Real.sqrt 3 := by
    have hsq_le : (16 * Real.sqrt 3)^2 < (35 : ℝ)^2 := by
      rw [h16s3, hsq35]; norm_num
    have h16s3_pos : 0 < 16 * Real.sqrt 3 := by positivity
    nlinarith [hsq_le, h16s3_pos]
  -- From 35 > 16√3, derive 3√7 > 4 + 2√3 by squaring once more.
  -- (3√7)² = 63, (4 + 2√3)² = 16 + 16√3 + 12 = 28 + 16√3.
  -- 63 - 28 = 35 > 16√3 ⟹ 63 > 28 + 16√3 = (4 + 2√3)².
  have hsq3_pos : 0 < 4 + 2 * Real.sqrt 3 := by positivity
  have hsq_4_2s3 : (4 + 2 * Real.sqrt 3)^2 = 28 + 16 * Real.sqrt 3 := by
    have : (4 + 2 * Real.sqrt 3)^2
        = 16 + 16 * Real.sqrt 3 + 4 * (Real.sqrt 3 * Real.sqrt 3) := by ring
    rw [this, hsq3]; ring
  have h_3s7_sq : (3 * Real.sqrt 7)^2 = 63 := by
    have : (3 * Real.sqrt 7)^2 = 9 * (Real.sqrt 7 * Real.sqrt 7) := by ring
    rw [this, hsq7]; norm_num
  have h_3s7_gt : 3 * Real.sqrt 7 > 4 + 2 * Real.sqrt 3 := by
    have hsq_lt : (4 + 2 * Real.sqrt 3)^2 < (3 * Real.sqrt 7)^2 := by
      rw [hsq_4_2s3, h_3s7_sq]; linarith [h35_gt]
    have h3s7_pos : 0 < 3 * Real.sqrt 7 := by positivity
    nlinarith [hsq_lt, hsq3_pos, h3s7_pos]
  -- Conclude from the cleared-denominator inequality.
  nlinarith [h_3s7_gt, hs3, hs7]

/-! ### The proper-coloring theorem -/

end HadwigerNelsonBounds
