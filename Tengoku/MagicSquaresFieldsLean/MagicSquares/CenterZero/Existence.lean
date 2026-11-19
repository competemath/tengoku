import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.Distinct
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.CubicJacobiBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Section 6 with no abstract Weil hypothesis

The previous center-zero theorem had one remaining input,
`HasCenterZeroCubicWeilBound F`.  The Jacobi-sum calculation now supplies
that input directly.
-/

/-- The paper's Section 6 existence theorem with the cubic character-sum
bound discharged internally.
@isnad1 id=ex.3h1v.s6.32d73267826b from=translated src=- shape=057ab950 vocab=721dab28
-/
theorem exists_centerZero_magic_of_squares_of_card_mod_four_one_unconditional
    (hodd : ringChar F ≠ 2)
    (hq : 77 ≤ Fintype.card F)
    (hqmod : Fintype.card F % 4 = 1) :
    ∃ M : Square3 F, IsMagicOfPowers 2 M := by
  have hWeil :
      HasCenterZeroCubicWeilBound F :=
    centerZeroCubicWeilBound_of_card_mod_four_one
      (F := F) hodd hqmod
  exact
    exists_centerZero_magic_of_squares_of_card_mod_four_one
      (F := F) hodd hWeil hq hqmod

end MagicSquares
