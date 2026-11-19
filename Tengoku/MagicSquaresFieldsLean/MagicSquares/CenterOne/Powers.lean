import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.Geometry
import Tengoku.MagicSquaresFieldsLean.MagicSquares.PowerResidue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {R : Type*} [CommRing R]

/-!
# Power conditions on the center-one line

The center entry is `1`, hence is automatically an `n`th power.  The
remaining problem is to make the eight values `1 + λt` into `n`th powers.
-/

theorem one_isNthPower (n : ℕ) :
    IsNthPower n (1 : R) := by
  refine ⟨1, ?_⟩
  simp

/-- If all nine linear forms `1 + λt` are `n`th powers, then the
center-one line is a magic square of distinct `n`th powers.-/
theorem centerOneLine_isMagicOfPowers
    [IsDomain R]
    (n : ℕ)
    {t b : R}
    (hb : CenterOneGoodB b)
    (ht : t ≠ 0)
    (hp : ∀ k : Fin 9, IsNthPower n (1 + centerOneCoeff b k * t)) :
    IsMagicOfPowers n (centerOneLine t b) := by
  refine ⟨centerOneLine_isMagic t b,
    centerOneLine_pairwiseDistinct hb ht, ?_⟩
  intro k
  rw [centerOneLine_entry_formula]
  exact hp k

/-- It is enough to check only the eight non-center entries, since the
center is `1`.-/
theorem centerOneLine_isMagicOfPowers_of_noncenter
    [IsDomain R]
    (n : ℕ)
    {t b : R}
    (hb : CenterOneGoodB b)
    (ht : t ≠ 0)
    (hp : ∀ k : Fin 9, k ≠ 4 →
      IsNthPower n (1 + centerOneCoeff b k * t)) :
    IsMagicOfPowers n (centerOneLine t b) := by
  apply centerOneLine_isMagicOfPowers n hb ht
  intro k
  by_cases hk : k = 4
  · subst k
    simpa [centerOneCoeff] using one_isNthPower (R := R) n
  · exact hp k hk

end Square3
end MagicSquares
