import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.RelationDegree
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.KummerBridge
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The easy degree-range part of quotient independence

Whenever the ordinary relation has degree `< q`, quotient vanishing
already implies ordinary polynomial vanishing.  The hard Kummer step is
precisely what is needed when the relation can reach or exceed degree
`q`.
-/

omit [Fintype F] in
/-- Quotient vanishing becomes an ordinary polynomial identity under
the explicit degree envelope `D + (m-1)G < q`.
@isnad1 id=eq.4h7v.s12.24fcdac48518 from=translated src=- shape=1db63929 vocab=ff5d379a
-/
theorem quotient_relation_polynomial_eq_zero_of_degree_range
    {m q D G : ℕ}
    (a : Fin m → Polynomial F)
    (g : Polynomial F)
    (ha : ∀ i, (a i).natDegree ≤ D)
    (hg : g.natDegree ≤ G)
    (hrange : D + (m - 1) * G < q)
    (hrel :
      ∑ i : Fin m,
        (AdjoinRoot.mk (X ^ q : Polynomial F)) (a i) *
          ((AdjoinRoot.mk (X ^ q : Polynomial F)) g) ^ (i : ℕ) = 0) :
    quotientPowerRelationPolynomial a g = 0 := by
  have hmk :
      (AdjoinRoot.mk (X ^ q : Polynomial F))
        (quotientPowerRelationPolynomial a g) = 0 := by
    rw [mk_relationPolynomial]
    exact hrel
  apply eq_zero_of_adjoinRoot_X_pow_eq_zero_of_natDegree_lt
    (F := F)
    (quotientPowerRelationPolynomial a g)
  · exact lt_of_le_of_lt
      (quotientPowerRelationPolynomial_natDegree_le
        (F := F) a g ha hg)
      hrange
  · exact hmk

end LN97
end MagicSquares
