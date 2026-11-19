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

/--
@isnad1 id=isnthpow.0h2v.s4.f073b539dbef from=translated src=- shape=182f3df2 vocab=3a623a90
-/
theorem one_isNthPower (n : ℕ) :
    IsNthPower n (1 : R) := by
  refine ⟨1, ?_⟩
  simp

/-- If all nine linear forms `1 + λt` are `n`th powers, then the
center-one line is a magic square of distinct `n`th powers.
@isnad1 id=ismagico.3h4v.s6.0ad0add78c77 from=translated src=- shape=8057e023 vocab=4be2bf8c
-/
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
center is `1`.
@isnad1 id=ismagico.3h4v.s7.e8933e60c19f from=translated src=- shape=cb20f280 vocab=4be2bf8c
-/
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
