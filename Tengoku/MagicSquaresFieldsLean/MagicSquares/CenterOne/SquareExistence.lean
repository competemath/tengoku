import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.Admissible
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.AnalyticInterfaces
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Bounds
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Section 7 after the character-sum estimate
-/

/-- The optimized Section 7 estimate gives more than nine square-good
parameters once `q ≥ 553736`.-/
theorem centerOne_square_parameters_card_gt_nine
    (hodd : ringChar F ≠ 2)
    (hCount : HasCenterOneSquareCountBound F)
    (hq : 553736 ≤ Fintype.card F) :
    ∃ b : F,
      CenterOneGoodB b ∧ 9 < (centerOnePowerParameters 2 b).card := by
  have hq7 : 7 < Fintype.card F := by omega
  obtain ⟨b, hb⟩ := exists_centerOneGoodB (F := F) hodd hq7
  have hlower := hCount b hb
  have hnum := centerOne_numeric_bound hq
  have hstrict :
      (2304 : ℝ) <
        (Fintype.card F : ℝ) - 28 -
          741 * Real.sqrt (Fintype.card F : ℝ) := by
    linarith
  have hmul :
      (2304 : ℝ) < 256 * ((centerOnePowerParameters 2 b).card : ℝ) :=
    lt_of_lt_of_le hstrict hlower
  have hcardR :
      (9 : ℝ) < ((centerOnePowerParameters 2 b).card : ℝ) := by
    nlinarith
  have hcard : 9 < (centerOnePowerParameters 2 b).card := by
    exact_mod_cast hcardR
  exact ⟨b, hb, hcard⟩

/-- Section 7 existence theorem, with its analytic Weil estimate isolated as
`HasCenterOneSquareCountBound F`.-/
theorem exists_centerOne_magic_of_squares_of_count_bound
    (hodd : ringChar F ≠ 2)
    (hCount : HasCenterOneSquareCountBound F)
    (hq : 553736 ≤ Fintype.card F) :
    ∃ M : Square3 F, IsMagicOfPowers 2 M := by
  obtain ⟨b, hb, hcard⟩ :=
    centerOne_square_parameters_card_gt_nine
      (F := F) hodd hCount hq
  obtain ⟨t, htpow, htbad⟩ :=
    exists_power_parameter_outside_bad (F := F) hcard
  exact exists_centerOne_magic_of_powers_of_parameter
    (F := F) 2 hb htpow htbad

/-- Consequently the field is not Parker.-/
theorem not_isParker_of_centerOne_bound
    (hodd : ringChar F ≠ 2)
    (hCount : HasCenterOneSquareCountBound F)
    (hq : 553736 ≤ Fintype.card F) :
    ¬ IsParker F := by
  intro hP
  apply hP
  exact exists_centerOne_magic_of_squares_of_count_bound
    (F := F) hodd hCount hq

end Square3
end MagicSquares
