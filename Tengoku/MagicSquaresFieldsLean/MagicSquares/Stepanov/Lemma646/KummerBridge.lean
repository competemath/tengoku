import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.Core
import Tengoku.Seed.RingTheory.AdjoinRoot
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F]

/-!
# LN97 Lemma 6.46: quotient-to-polynomial bridge

`QuotientPowerIndependent` is currently formulated modulo `X^q`.
Before the Kummer / absolute-irreducibility argument can be attached,
one needs the elementary observation that a polynomial of degree `< q`
which is zero modulo `X^q` is already the zero polynomial.

This file proves that bridge.  It removes one quotient-ring layer from
the remaining Lemma 6.46 problem.
-/

/-- A polynomial of natural degree `< q` cannot vanish in
`F[X]/(X^q)` unless it is zero.-/
theorem eq_zero_of_adjoinRoot_X_pow_eq_zero_of_natDegree_lt
    {q : ℕ} (P : Polynomial F)
    (hdeg : P.natDegree < q)
    (hmk :
      (AdjoinRoot.mk (X ^ q : Polynomial F)) P = 0) :
    P = 0 := by
  by_contra hP
  have hmonic : (X ^ q : Polynomial F).Monic :=
    Polynomial.monic_X.pow q
  have hdeg' :
      P.natDegree < (X ^ q : Polynomial F).natDegree := by
    simpa using hdeg
  have hne :=
    AdjoinRoot.mk_ne_zero_of_natDegree_lt hmonic hP hdeg'
  exact hne hmk

/-- Consequently, any relation represented in the quotient by a
polynomial whose total degree is `< q` is an actual polynomial relation.

This is intended for the first-block relation in Lemma 6.46 after its
degree bound has been established.
@isnad1 id=eq.2h3v.s10.a90a6a9c996d from=translated src=- shape=0058de25 vocab=7d3e7b61
-/
theorem actual_relation_of_quotient_relation
    {q : ℕ} (P : Polynomial F)
    (hdeg : P.natDegree < q)
    (hrel :
      (AdjoinRoot.mk (X ^ q : Polynomial F)) P = 0) :
    P = 0 :=
  eq_zero_of_adjoinRoot_X_pow_eq_zero_of_natDegree_lt
    (F := F) P hdeg hrel

end LN97
end MagicSquares
