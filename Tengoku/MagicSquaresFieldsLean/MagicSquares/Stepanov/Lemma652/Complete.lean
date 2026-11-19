import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.Complete
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.DerivativeDataConstruct
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.ConcreteConstraints
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.VariableConstraints
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.BookArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Lidl--Niederreiter Lemma 6.52

The variable degree constraints supply a nonzero coefficient vector.
The completed Lemma 6.46 makes its auxiliary polynomial nonzero directly;
no quotient-independence hypothesis is required.  The derivative expansion
gives multiplicity at least `M` both at roots of `B(g)` and at roots of `f`.
Finally, the book's numerical hypotheses imply the dimension inequality
and the strict degree bound.
-/

end LN97
end MagicSquares
