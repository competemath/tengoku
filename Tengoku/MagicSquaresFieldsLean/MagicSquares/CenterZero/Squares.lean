import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.CharacterSum
import Tengoku.MagicSquaresFieldsLean.MagicSquares.PowerResidue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

omit [Fintype F] [DecidableEq F] in
/-- For exponent two, our `IsNthPower` predicate is exactly mathlib's
`IsSquare`.
@isnad1 id=iff.0h2v.s5.1a297ec7e8d0 from=translated src=- shape=1b1fedbb vocab=444c9658
-/
theorem isNthPower_two_iff_isSquare (x : F) :
    IsNthPower 2 x ↔ IsSquare x := by
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact IsSquare.sq y
  · intro hx
    rcases hx.exists_sq with ⟨y, hy⟩
    exact ⟨y, hy.symm⟩

/-- A nonzero Section 6 weight, away from the three zero locations, forces
all three quadratic characters to equal `1`.  This is the exact formal
version of the statement that the product indicator is either zero or one
away from `x = -1, 0, 1`.
@isnad1 id=and.4h2v.s8.a538c1494840 from=translated src=- shape=9a19f32d vocab=c1e46c32
-/
theorem centerZeroWeight_ne_zero_forces_char_one
    (x : F)
    (hxm1 : x ≠ 1)
    (hx0 : x ≠ 0)
    (hxp1 : x ≠ -1)
    (hw : centerZeroWeight x ≠ 0) :
    χ (x - 1) = 1 ∧ χ x = 1 ∧ χ (x + 1) = 1 := by
  have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hxm1
  have hadd : x + 1 ≠ 0 := by
    intro h
    apply hxp1
    linear_combination h

  have hf1 : 1 + χ (x - 1) ≠ 0 := by
    intro hz
    apply hw
    change (1 + χ (x - 1)) * (1 + χ x) * (1 + χ (x + 1)) = 0
    rw [hz]
    simp
  have hf2 : 1 + χ x ≠ 0 := by
    intro hz
    apply hw
    change (1 + χ (x - 1)) * (1 + χ x) * (1 + χ (x + 1)) = 0
    rw [hz]
    simp
  have hf3 : 1 + χ (x + 1) ≠ 0 := by
    intro hz
    apply hw
    change (1 + χ (x - 1)) * (1 + χ x) * (1 + χ (x + 1)) = 0
    rw [hz]
    simp

  have hc1 : χ (x - 1) = 1 := by
    rcases quadraticChar_dichotomy hsub with h | h
    · exact h
    · exfalso
      apply hf1
      simp [h]
  have hc2 : χ x = 1 := by
    rcases quadraticChar_dichotomy hx0 with h | h
    · exact h
    · exfalso
      apply hf2
      simp [h]
  have hc3 : χ (x + 1) = 1 := by
    rcases quadraticChar_dichotomy hadd with h | h
    · exact h
    · exfalso
      apply hf3
      simp [h]
  exact ⟨hc1, hc2, hc3⟩

/-- Consequently the three consecutive elements are nonzero squares.
@isnad1 id=and.4h2v.s7.e74205efa27a from=translated src=- shape=111715a0 vocab=0a15668b
-/
theorem centerZeroWeight_ne_zero_forces_squares
    (x : F)
    (hxm1 : x ≠ 1)
    (hx0 : x ≠ 0)
    (hxp1 : x ≠ -1)
    (hw : centerZeroWeight x ≠ 0) :
    IsSquare (x - 1) ∧ IsSquare x ∧ IsSquare (x + 1) := by
  obtain ⟨hc1, hc2, hc3⟩ :=
    centerZeroWeight_ne_zero_forces_char_one (F := F) x hxm1 hx0 hxp1 hw
  have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hxm1
  have hadd : x + 1 ≠ 0 := by
    intro h
    apply hxp1
    linear_combination h
  exact ⟨
    (quadraticChar_one_iff_isSquare hsub).mp hc1,
    (quadraticChar_one_iff_isSquare hx0).mp hc2,
    (quadraticChar_one_iff_isSquare hadd).mp hc3
  ⟩

omit [Fintype F] [DecidableEq F] in
/-- If `-1`, `x-1`, `x`, and `x+1` are squares, then every entry of the
center-zero family is a square.  This isolates the sign argument in
Section 6 from the later distinctness/counting argument.
@isnad1 id=isnthpow.4h3v.s7.9be0f0ea1db5 from=translated src=- shape=48e7cf9c vocab=62206b94
-/
theorem centerZero_all_entries_are_squares
    (x : F)
    (hneg : IsSquare (-1 : F))
    (hxm : IsSquare (x - 1))
    (hx : IsSquare x)
    (hxp : IsSquare (x + 1)) :
    ∀ k : Fin 9, IsNthPower 2 ((Square3.centerZero x).entries k) := by
  have hnegx : IsSquare (-x) := by
    simpa using hneg.mul hx
  have hnegxm : IsSquare (1 - x) := by
    simpa [neg_sub] using hneg.mul hxm
  have hnegxp : IsSquare (-x - 1) := by
    have heq : (-1 : F) * (x + 1) = -x - 1 := by
      ring
    rw [← heq]
    exact hneg.mul hxp

  intro k
  fin_cases k <;>
    simp [Square3.entries, isNthPower_two_iff_isSquare,
      hnegx, hnegxm, hnegxp, hneg, hxm, hx, hxp]

end MagicSquares
