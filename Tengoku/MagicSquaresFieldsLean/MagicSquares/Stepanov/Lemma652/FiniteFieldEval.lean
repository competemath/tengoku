import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

variable {F : Type*} [Field F] [Fintype F]

/-!
# Frobenius evaluation over the finite base field

The transition from (6.25) to the polynomials `s_{t,n}` uses the fact
that for every `c ∈ F_q`, one has `c^q = c`.  Thus the factors
`c^(qj)` become `c^j` after evaluation.
-/

/-- Every element of a finite field satisfies `c^q = c`, where
`q = |F|`.-/
theorem finiteField_pow_card (c : F) :
    c ^ Fintype.card F = c := by
  simpa using (FiniteField.pow_card_pow (K := F) 1 c)

/-- Consequently `(c^q)^j = c^j`.-/
theorem finiteField_pow_card_pow_eq (c : F) (j : ℕ) :
    (c ^ Fintype.card F) ^ j = c ^ j := by
  rw [finiteField_pow_card]

/-- Equivalent exponent-multiplication form.-/
theorem finiteField_pow_card_mul_eq (c : F) (j : ℕ) :
    c ^ (Fintype.card F * j) = c ^ j := by
  rw [pow_mul, finiteField_pow_card]

end LN97
end MagicSquares
