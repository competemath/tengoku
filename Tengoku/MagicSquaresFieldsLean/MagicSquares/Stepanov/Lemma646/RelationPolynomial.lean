import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.Core
import Tengoku.Seed.RingTheory.AdjoinRoot
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Lifting the first-block relation out of F[X]/(X^q)

The quotient-ring relation in `QuotientPowerIndependent` is equivalent
to saying that `X^q` divides the ordinary polynomial relation

    Σ_i a_i g^i.

This is a useful concrete starting point for the remaining Kummer /
absolute-irreducibility argument of Lemma 6.46.
-/

/-- The ordinary polynomial represented by a first-block relation.-/
noncomputable def quotientPowerRelationPolynomial
    {m : ℕ}
    (a : Fin m → Polynomial F)
    (g : Polynomial F) :
    Polynomial F :=
  ∑ i : Fin m, a i * g ^ (i : ℕ)

omit [Fintype F] [DecidableEq F] in
/-- Mapping the ordinary relation polynomial to `AdjoinRoot (X^q)`
gives exactly the quotient relation used in
`QuotientPowerIndependent`.-/
theorem mk_relationPolynomial
    {m q : ℕ}
    (a : Fin m → Polynomial F)
    (g : Polynomial F) :
    (AdjoinRoot.mk (X ^ q : Polynomial F))
      (quotientPowerRelationPolynomial a g)
      =
    ∑ i : Fin m,
      (AdjoinRoot.mk (X ^ q : Polynomial F)) (a i) *
        ((AdjoinRoot.mk (X ^ q : Polynomial F)) g) ^ (i : ℕ) := by
  simp [quotientPowerRelationPolynomial]

omit [Fintype F] [DecidableEq F] in
/-- A quotient relation is equivalent to divisibility of its ordinary
representative by `X^q`.-/
theorem quotientRelation_iff_X_pow_dvd
    {m q : ℕ}
    (a : Fin m → Polynomial F)
    (g : Polynomial F) :
    (∑ i : Fin m,
      (AdjoinRoot.mk (X ^ q : Polynomial F)) (a i) *
        ((AdjoinRoot.mk (X ^ q : Polynomial F)) g) ^ (i : ℕ) = 0)
      ↔
    (X ^ q : Polynomial F) ∣
      quotientPowerRelationPolynomial a g := by
  rw [← mk_relationPolynomial (F := F) a g]
  exact AdjoinRoot.mk_eq_zero

end LN97
end MagicSquares
