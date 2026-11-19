import Tengoku.MagicSquaresFieldsLean.MagicSquares.Jacobi.Characters
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Data.Fintype.Sets
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The square-fiber identity

For odd finite fields the number of square roots of `y` is
`1 + χ(y)`.  Summing a function through the squaring map therefore gives

    ∑_x f(x²) = ∑_y (1 + χ(y)) f(y).

We use the complexified quadratic character so this can feed directly into
the Jacobi-sum calculation.
-/

/-- Fiberwise summation through the squaring map, with the fiber cardinality
written using the complex quadratic character.
@isnad1 id=eq.1h2v.s7.6d028606e249 from=translated src=- shape=8a658c89 vocab=f8fe07bd
-/
theorem sum_over_squares_via_quadraticCharC
    (hodd : ringChar F ≠ 2)
    (f : F → ℂ) :
    (∑ x : F, f (x ^ 2)) =
      ∑ y : F, (1 + quadraticCharC F y) * f y := by
  calc
    (∑ x : F, f (x ^ 2))
        = ∑ y : F,
            ∑ x ∈ (Finset.univ : Finset F) with x ^ 2 = y, f y := by
          symm
          simpa using
            (Finset.sum_fiberwise'
              (Finset.univ : Finset F)
              (fun x : F => x ^ 2) f)
    _ = ∑ y : F, (1 + quadraticCharC F y) * f y := by
          apply Finset.sum_congr rfl
          intro y hy
          have hrootFinset :
              {x : F | x ^ 2 = y}.toFinset =
                Finset.univ.filter (fun x : F => x ^ 2 = y) := by
            ext x
            simp
          have hcardZ :
              (((Finset.univ.filter fun x : F => x ^ 2 = y).card : ℕ) : ℤ)
                = quadraticChar F y + 1 := by
            have h := quadraticChar_card_sqrts (F := F) hodd y
            rw [hrootFinset] at h
            exact h
          have hcardC :
              (((Finset.univ.filter fun x : F => x ^ 2 = y).card : ℕ) : ℂ)
                = 1 + quadraticCharC F y := by
            have h :=
              congrArg (fun z : ℤ => (z : ℂ)) hcardZ
            simpa [quadraticCharC, add_comm] using h
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [hcardC]

end MagicSquares
