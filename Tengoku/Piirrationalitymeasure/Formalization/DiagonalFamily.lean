import Tengoku.Piirrationalitymeasure.Formalization.OldPointPartition
import Tengoku.Piirrationalitymeasure.Formalization.ParameterStationary
import Tengoku.Piirrationalitymeasure.Formalization.ConstructionIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact arithmetic of the tight-slack family (6.34)--(6.39). -/

namespace PiIrrationality

theorem diagonalFamily_slacks (M : ℕ) (hM : 6 ≤ M) :
    M + 2 * M - (3 * M - 1) = 1 ∧
    2 * (2 * M) - (3 * M - 1) = M + 1 ∧
    (5 * (3 * M - 1) - 1) - 7 * (2 * M) = M - 6 ∧
    (2 * M + 4 * (2 * M) - 2 * (3 * M - 1)) - ((3 * M - 1) + 1) = M + 2 ∧
    7 * (2 * M) ≤ 5 * (3 * M - 1) - 1 ∧
    M + 2 * (2 * M) - (3 * M - 1) = 2 * M + 1 ∧
    2 * M + 4 * (2 * M) - 2 * (3 * M - 1) = 4 * M + 2 := by
  omega

theorem diagonalFamily_exponent (M : ℝ) (hM : 1 / 3 < M) :
    2 * M / (3 * M - 1) = 2 / 3 + 2 / (3 * (3 * M - 1)) := by
  have hden : 3 * M - 1 ≠ 0 := by linarith
  apply (mul_right_inj' hden).mp
  field_simp [hden]
  ring

theorem diagonalFamily_admissible (M : ℕ) (hM : 6 ≤ M) :
    Admissible (constructionParameter M (2 * M) (3 * M - 1)) := by
  have hM' : (6 : ℝ) ≤ M := by exact_mod_cast hM
  have he : ((3 * M - 1 : ℕ) : ℝ) = 3 * (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hden : 0 < 3 * (M : ℝ) - 1 := by linarith
  dsimp [Admissible, constructionParameter]
  rw [he]
  push_cast
  constructor
  · rw [← add_div]
    change 1 < (M + 2 * (M : ℝ)) / (3 * M - 1)
    rw [lt_div_iff₀ hden]
    linarith
  constructor
  · rw [← mul_div_assoc]
    change 1 < 2 * (2 * (M : ℝ)) / (3 * M - 1)
    rw [lt_div_iff₀ hden]
    nlinarith
  constructor
  · rw [← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith
  · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    have h : (3 : ℝ) < (2 * M + 4 * (2 * M)) / (3 * M - 1) := by
      rw [lt_div_iff₀ hden]
      nlinarith
    linarith

theorem diagonalFamily_stationary (M y : ℝ) (hM : 1 / 3 < M) :
    (3 * M - 1) * parameterStationary (M / (3 * M - 1), 2 * M / (3 * M - 1)) y =
      (2 * M + 1) * y ^ 3 - (125 * M - 6) * y ^ 2 - (500 * M - 25) * y - 625 * M := by
  have hden : 3 * M - 1 ≠ 0 := by linarith
  dsimp [parameterStationary]
  field_simp [hden]
  ring

theorem candidate_on_oldPoint_direction :
    candidate = oldPoint + (1 / 8355 : ℝ) • ((1 : ℝ) / 2, 1) ∧
    (3714 : ℝ) / 5570 = 1857 / 2785 ∧
    (1857 : ℝ) / 2785 = 2 / 3 + 1 / 8355 := by
  constructor
  · ext <;> norm_num [candidate, oldPoint]
  · constructor <;> norm_num

end PiIrrationality
