import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.AbsoluteIrreducibility
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.BlockTranslation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-!
# Lidl--Niederreiter Lemma 6.46

This completes the block-independence lemma from the book's absolute
irreducibility hypothesis, including the case `f(0) = 0`.

The final theorem writes the book's coefficient-degree allowance without
truncated subtraction: every nonzero coefficient `e` satisfies
`m * (natDegree e + natDegree f) ≤ q`.  For nonzero `e`, this is precisely
`deg e ≤ q/m - deg f`.  Zero coefficients are allowed in every degree
range.  Consequently the theorem also covers a negative allowance.
-/

end LN97
end MagicSquares
