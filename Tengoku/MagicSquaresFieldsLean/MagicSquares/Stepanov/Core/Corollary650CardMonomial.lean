import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.Corollary650FiniteField
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-!
# Corollary 6.50 in the termwise form needed for (6.25)

For every `n < q = |F|`, including `n = 0`,

    E^(n)(w (X^q)^j) = E^(n)(w) (X^q)^j.

The positive-order case is exactly the Frobenius-monomial lemma already
proved in `StepanovCorollary650`; the zero-order case is simp.
-/

/-- Termwise finite-field-cardinality version of Corollary 6.50.
@isnad1 id=eq.1h4v.s10.9c9b3e06747e from=translated src=- shape=25f38267 vocab=798f4e4e
-/
theorem hasseDeriv_mul_cardMonomial
    (n : ℕ)
    (hnlt : n < Fintype.card F)
    (w : Polynomial F)
    (j : ℕ) :
    (hasseDeriv n)
        (w * (X ^ Fintype.card F : Polynomial F) ^ j) =
      (hasseDeriv n) w *
        (X ^ Fintype.card F : Polynomial F) ^ j := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨p, hpchar, s, hp, hcard⟩ := FiniteField.card' F
    letI : CharP F p := hpchar
    have hnlt' : n < p ^ (s : ℕ) := by
      simpa [hcard] using hnlt
    simpa [hcard] using
      (hasseDeriv_mul_frobeniusMonomial
        (K := F) hp hnpos hnlt' w j)

end LN97
end MagicSquares
