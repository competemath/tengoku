import Tengoku.MagicSquaresFieldsLean.MagicSquares.Jacobi.CubicIdentity
import Tengoku.MagicSquaresFieldsLean.MagicSquares.WeilInterface
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Closing the Section 6 cubic Weil estimate by Jacobi sums

This is specialized to the exact cubic polynomial appearing in the paper.
It avoids carrying the full general Stepánov theorem through the final
Section 6 argument.
-/

/-- The complexified cubic quadratic-character sum has norm at most
`2 sqrt(#F)` when `#F ≡ 1 (mod 4)`.
@isnad1 id=le.2h1v.s7.89e20287814e from=translated src=- shape=c9e690bc vocab=8362dc6c
-/
theorem cubic_quadratic_sum_norm_le
    (hodd : ringChar F ≠ 2)
    (hqmod : Fintype.card F % 4 = 1) :
    ‖∑ x : F,
        quadraticCharC F ((x - 1) * x * (x + 1))‖
      ≤ 2 * Real.sqrt (Fintype.card F : ℝ) := by
  obtain ⟨chi4, hchi4⟩ :=
    exists_quartic_mulChar (F := F) hqmod
  let η : MulChar F ℂ := quadraticCharC F

  have hηsq : η ^ 2 = 1 := by
    simpa [η] using
      quadraticCharC_sq_eq_one (F := F)
  have hηmul : η * η = 1 := by
    simpa [pow_two] using hηsq
  have hchi4ne : chi4 ≠ 1 :=
    quartic_ne_one (F := F) hchi4
  have hηne : η ≠ 1 := by
    simpa [η] using
      quadraticCharC_ne_one (F := F) hodd

  have hchi4ηne : chi4 * η ≠ 1 := by
    intro h
    have hleq : chi4 = η := by
      calc
        chi4 = chi4 * 1 := by simp
        _ = chi4 * (η * η) := by rw [hηmul]
        _ = (chi4 * η) * η := by group
        _ = η := by rw [h]; simp
    have hsquare : chi4 ^ 2 = 1 := by
      rw [hleq]
      exact hηsq
    exact (quartic_sq_ne_one (F := F) hchi4) hsquare

  have hchi4ηηne : (chi4 * η) * η ≠ 1 := by
    intro h
    apply hchi4ne
    calc
      chi4 = chi4 * 1 := by simp
      _ = chi4 * (η * η) := by rw [hηmul]
      _ = (chi4 * η) * η := by group
      _ = 1 := h

  have hJ1 :
      ‖jacobiSum chi4 η‖ =
        Real.sqrt (Fintype.card F : ℝ) :=
    jacobiSum_norm_eq_sqrt_card
      (F := F) hchi4ne hηne hchi4ηne

  have hJ2 :
      ‖jacobiSum (chi4 * η) η‖ =
        Real.sqrt (Fintype.card F : ℝ) :=
    jacobiSum_norm_eq_sqrt_card
      (F := F) hchi4ηne hηne hchi4ηηne

  have hid :
      (∑ x : F,
          quadraticCharC F ((x - 1) * x * (x + 1))) =
        jacobiSum chi4 η + jacobiSum (chi4 * η) η := by
    simpa [η] using
      cubic_quadratic_sum_eq_two_jacobiSums
        (F := F) hodd hqmod hchi4

  rw [hid]
  calc
    ‖jacobiSum chi4 η + jacobiSum (chi4 * η) η‖
        ≤ ‖jacobiSum chi4 η‖ + ‖jacobiSum (chi4 * η) η‖ :=
          norm_add_le _ _
    _ = 2 * Real.sqrt (Fintype.card F : ℝ) := by
          rw [hJ1, hJ2]
          ring

/-- Real/integer form of the same bound, matching the existing
`HasCenterZeroCubicWeilBound` interface.
@isnad1 id=le.2h1v.s7.5a227e684389 from=translated src=- shape=b2bdd355 vocab=ee9cd39f
-/
theorem centerZeroCubicCharacterSum_abs_le
    (hodd : ringChar F ≠ 2)
    (hqmod : Fintype.card F % 4 = 1) :
    |(((∑ x : F,
        quadraticChar F ((x - 1) * x * (x + 1)) : ℤ) : ℝ))|
      ≤ 2 * Real.sqrt (Fintype.card F : ℝ) := by
  have hnorm :=
    cubic_quadratic_sum_norm_le
      (F := F) hodd hqmod
  have hcast :
      (∑ x : F,
          quadraticCharC F ((x - 1) * x * (x + 1))) =
        ((∑ x : F,
            quadraticChar F ((x - 1) * x * (x + 1)) : ℤ) : ℂ) := by
    simp [quadraticCharC]
  rw [hcast] at hnorm
  rw [Complex.norm_intCast] at hnorm
  exact hnorm

/-- The formerly explicit cubic Weil hypothesis used by the center-zero
proof is automatic in the `q ≡ 1 (mod 4)` case.
@isnad1 id=hascente.2h1v.s5.eb8fd76c76fb from=translated src=- shape=aad56ed2 vocab=ea23a823
-/
theorem centerZeroCubicWeilBound_of_card_mod_four_one
    (hodd : ringChar F ≠ 2)
    (hqmod : Fintype.card F % 4 = 1) :
    HasCenterZeroCubicWeilBound F := by
  exact centerZeroCubicCharacterSum_abs_le
    (F := F) hodd hqmod

end MagicSquares
