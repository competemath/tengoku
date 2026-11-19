import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.Corollary650
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-!
# Corollary 6.50 with q = |F|

The existing formalization of LN97 Corollary 6.50 is stated for the
Frobenius exponent `p^s`.  For the Stepanov application the exponent is
`q = |F|`.  A finite field has cardinality `p^s` for its characteristic
prime, so this file packages the exact specialization used in Lemma 6.52.
-/

/-- **LN97 Corollary 6.50, finite-field-cardinality form.**

For `0 < n < |F|`, differentiating after substituting `y = X^|F|`
is the same as taking the coefficientwise Hasse derivative first.
@isnad1 id=eq.2h3v.s8.1b565c9be5d6 from=translated src=- shape=9ea7a089 vocab=fef077a7
-/
theorem ln97_6_50_finiteField
    (n : ℕ)
    (hnpos : 0 < n)
    (hnlt : n < Fintype.card F)
    (v : Polynomial (Polynomial F)) :
    (hasseDeriv n) (substYXPow (Fintype.card F) v) =
      substYXPow (Fintype.card F) (partialHasseX n v) := by
  obtain ⟨p, hpchar, s, hp, hcard⟩ := FiniteField.card' F
  letI : CharP F p := hpchar
  have hnlt' : n < p ^ (s : ℕ) := by
    simpa [hcard] using hnlt
  have h := ln97_6_50 (K := F) hp hnpos hnlt' v
  simpa [hcard] using h

/-- The order-zero case of Corollary 6.50, which is needed because
Lemma 6.52 imposes derivative conditions for `0 ≤ n < M`.
@isnad1 id=eq.0h2v.s8.fcab077a1f08 from=translated src=- shape=e9a7d061 vocab=51dd6f27
-/
theorem ln97_6_50_finiteField_zero
    (v : Polynomial (Polynomial F)) :
    (hasseDeriv 0) (substYXPow (Fintype.card F) v) =
      substYXPow (Fintype.card F) (partialHasseX 0 v) := by
  simp [partialHasseX, substYXPow]

end LN97
end MagicSquares
