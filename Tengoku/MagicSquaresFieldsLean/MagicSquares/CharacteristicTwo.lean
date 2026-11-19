import Tengoku.MagicSquaresFieldsLean.MagicSquares.PowerResidue
import Tengoku.Seed.Algebra.CharP.Two

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {R : Type*} [CommRing R] [CharP R 2]

/-- In characteristic two, the top-left and bottom-right entries of every
3 × 3 magic square coincide.-/
theorem a_eq_i_of_charTwo (M : Square3 R) (hM : IsMagic M) : M.a = M.i := by
  rw [universal_form M hM]
  simp [parametrized, CharTwo.sub_eq_add]

/-- Consequently, no 3 × 3 magic square in characteristic two has nine
distinct entries.-/
theorem not_pairwiseDistinct_of_charTwo (M : Square3 R) (hM : IsMagic M) :
    ¬ M.PairwiseDistinct := by
  intro hdist
  have hEntries : M.entries (0 : Fin 9) = M.entries (8 : Fin 9) := by
    simpa [entries] using a_eq_i_of_charTwo M hM
  have hIndex : (0 : Fin 9) = (8 : Fin 9) := hdist hEntries
  exact (by decide : (0 : Fin 9) ≠ (8 : Fin 9)) hIndex

end Square3

/-- Section 16, strengthened slightly: over any commutative ring of
characteristic two, the distinct-entry obstruction makes the ring `n`-Parker
for every exponent `n`.-/
theorem isNParker_of_charTwo {R : Type*} [CommRing R] [CharP R 2] (n : ℕ) :
    IsNParker R n := by
  rintro ⟨M, hMagic, hDistinct, hPowers⟩
  exact Square3.not_pairwiseDistinct_of_charTwo M hMagic hDistinct

end MagicSquares
