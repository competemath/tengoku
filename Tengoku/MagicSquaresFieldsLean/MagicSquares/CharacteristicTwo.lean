import Tengoku.MagicSquaresFieldsLean.MagicSquares.PowerResidue
import Tengoku.Seed.Algebra.CharP.Two

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {R : Type*} [CommRing R] [CharP R 2]

/-- In characteristic two, the top-left and bottom-right entries of every
3 × 3 magic square coincide.
@isnad1 id=eq.1h2v.s5.6c3064748e76 from=translated src=- shape=7df47f31 vocab=f30f4d3e
-/
theorem a_eq_i_of_charTwo (M : Square3 R) (hM : IsMagic M) : M.a = M.i := by
  rw [universal_form M hM]
  simp [parametrized, CharTwo.sub_eq_add]

/-- Consequently, no 3 × 3 magic square in characteristic two has nine
distinct entries.
@isnad1 id=not.1h2v.s5.09e482d19ded from=translated src=- shape=80b28d88 vocab=bf9e79a2
-/
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
for every exponent `n`.
@isnad1 id=isnparke.0h2v.s4.5e9e5a20f3d0 from=translated src=- shape=b7ea3f74 vocab=b98fac20
-/
theorem isNParker_of_charTwo {R : Type*} [CommRing R] [CharP R 2] (n : ℕ) :
    IsNParker R n := by
  rintro ⟨M, hMagic, hDistinct, hPowers⟩
  exact Square3.not_pairwiseDistinct_of_charTwo M hMagic hDistinct

end MagicSquares
