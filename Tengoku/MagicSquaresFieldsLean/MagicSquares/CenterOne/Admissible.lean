import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.Forbidden
import Tengoku.Seed.Algebra.CharP.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The seven forbidden values are exactly enough

Outside `{0, ±1, ±2, ±1/2}`, the nine coefficients of the center-one
line (including the center coefficient `0`) are pairwise distinct.

This version avoids the previous giant `simp_all` search.  After the two
indices are enumerated, each possible collision is reduced by
`linear_combination` to one of the finitely many forbidden linear equations.
-/

section admissibleProof

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

omit [Fintype F] in
/-- The paper's seven exclusions imply the coefficient injectivity needed for
all later center-one constructions.-/
theorem centerOneGoodB_of_not_mem_forbidden
    (hodd : ringChar F ≠ 2)
    {b : F}
    (hb : b ∉ (centerOneForbiddenB : Finset F)) :
    CenterOneGoodB b := by
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hbn :
      b ≠ 0 ∧ b ≠ 1 ∧ b ≠ -1 ∧ b ≠ 2 ∧ b ≠ -2 ∧
      b ≠ (1 : F) / 2 ∧ b ≠ -(1 : F) / 2 := by
    simpa [centerOneForbiddenB, not_or] using hb
  rcases hbn with ⟨hb0, hb1, hbm1, hb2, hbm2, hbhalf, hbmhalf⟩

  have h2b0 : 2 * b ≠ (0 : F) := mul_ne_zero htwo hb0

  have h2b1 : 2 * b ≠ (1 : F) := by
    intro h
    apply hbhalf
    apply (eq_div_iff htwo).2
    simpa [mul_comm] using h

  have h2bm1 : 2 * b ≠ (-1 : F) := by
    intro h
    apply hbmhalf
    have heq : b = (-1 : F) / 2 := by
      apply (eq_div_iff htwo).2
      simpa [mul_comm] using h
    simpa [neg_div] using heq

  have h2b2 : 2 * b ≠ (2 : F) := by
    intro h
    apply hb1
    apply mul_left_cancel₀ htwo
    simpa using h

  have h2bm2 : 2 * b ≠ (-2 : F) := by
    intro h
    apply hbm1
    apply mul_left_cancel₀ htwo
    calc
      2 * b = -2 := h
      _ = 2 * (-1 : F) := by ring

  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [centerOneCoeff] at hij ⊢

  all_goals
    first
    | exact one_ne_zero (by linear_combination hij)
    | exact one_ne_zero (by linear_combination hij.symm)
    | exact hb0 (by linear_combination hij)
    | exact hb0 (by linear_combination hij.symm)
    | exact hb1 (by linear_combination hij)
    | exact hb1 (by linear_combination hij.symm)
    | exact hbm1 (by linear_combination hij)
    | exact hbm1 (by linear_combination hij.symm)
    | exact hb2 (by linear_combination hij)
    | exact hb2 (by linear_combination hij.symm)
    | exact hbm2 (by linear_combination hij)
    | exact hbm2 (by linear_combination hij.symm)
    | exact h2b0 (by linear_combination hij)
    | exact h2b0 (by linear_combination hij.symm)
    | exact h2b1 (by linear_combination hij)
    | exact h2b1 (by linear_combination hij.symm)
    | exact h2bm1 (by linear_combination hij)
    | exact h2bm1 (by linear_combination hij.symm)
    | exact h2b2 (by linear_combination hij)
    | exact h2b2 (by linear_combination hij.symm)
    | exact h2bm2 (by linear_combination hij)
    | exact h2bm2 (by linear_combination hij.symm)
    | exact htwo (by linear_combination hij)
    | exact htwo (by linear_combination hij.symm)

end admissibleProof

/-- For every odd finite field with more than seven elements there is a good
coefficient parameter `b`.-/
theorem exists_centerOneGoodB
    (hodd : ringChar F ≠ 2)
    (hq : 7 < Fintype.card F) :
    ∃ b : F, CenterOneGoodB b := by
  obtain ⟨b, hb⟩ := exists_not_mem_centerOneForbiddenB (F := F) hq
  exact ⟨b, centerOneGoodB_of_not_mem_forbidden (F := F) hodd hb⟩

end Square3
end MagicSquares
