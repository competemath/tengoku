import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.Representation
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.CoarseMultiplicative
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.ExponentReduction
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.PowerSum
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.SharpInterface

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sharp split multiplicative-character bound from LN97

The proof follows the roles of LN97 Theorems 5.39, 6.56, and 5.41:
1. Represent extension-field sums by powers of finitely many reciprocal roots.
2. Apply the coarse Stepanov bound uniformly over finite extensions.
3. Use Lemma 6.55 to bound each reciprocal root by sqrt(q).
4. Sum those bounds; the L-polynomial has degree at most r - 1.

The primitive-exponent theorem carries out this argument. Exponent reduction
then handles the general repeated-root case, and squarefree specialization
provides the simpler interface. No sharp bound is assumed as an extra axiom.
-/

namespace MagicSquares.LN97

open scoped BigOperators Classical
open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

end MagicSquares.LN97
