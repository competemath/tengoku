import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.Multiplicity
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-!
# A reusable strict cardinality bound for Theorem 6.53

LN97 obtains a strict degree estimate `deg h < D`; together with
`M |T| ≤ deg h`, this gives `M |T| < D`.

This tiny bridge will be used repeatedly for the two choices of `B` in
Theorem 6.53.
-/

/--
@isnad1 id=lt.3h5v.s6.9d949654ca79 from=translated src=- shape=7088ade3 vocab=e977e4fc
-/
theorem card_mul_lt_of_multiplicity_and_natDegree_lt
    (h : Polynomial F) (T : Finset F)
    (M D : ℕ)
    (hM : 0 < M)
    (hmult : ∀ c ∈ T, M ≤ rootMultiplicity c h)
    (hdeg : h.natDegree < D) :
    M * T.card < D := by
  exact lt_of_le_of_lt
    (card_mul_le_natDegree_of_rootMultiplicity
      (F := F) h T M hM hmult)
    hdeg

end LN97
end MagicSquares
