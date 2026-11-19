import Tengoku.MagicSquaresFieldsLean.MagicSquares.Jacobi.SquareFibers
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Jacobi.Norm
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The cubic quadratic-character sum as two Jacobi sums

For a quartic character `chi4`, put `η = chi4²`, so `η` is the quadratic
character.  The square-fiber identity applied to

    f(t) = chi4(t) η(t-1)

gives

    ∑_x η((x-1)x(x+1))
      = J(chi4,η) + J(chi4η,η)

when `η(-1)=1`.
-/

/-- The exact Jacobi-sum identity for the cubic Section 6 sum.-/
theorem cubic_quadratic_sum_eq_two_jacobiSums
    (hodd : ringChar F ≠ 2)
    (hqmod : Fintype.card F % 4 = 1)
    {chi4 : MulChar F ℂ}
    (hchi4 : orderOf chi4 = 4) :
    (∑ x : F,
        quadraticCharC F ((x - 1) * x * (x + 1))) =
      jacobiSum chi4 (quadraticCharC F) +
        jacobiSum (chi4 * quadraticCharC F) (quadraticCharC F) := by
  let η : MulChar F ℂ := quadraticCharC F
  have hchi4sq : chi4 ^ 2 = η := by
    simpa [η] using
      quartic_sq_eq_quadraticCharC
        (F := F) hodd hchi4
  have hηneg : η (-1) = 1 := by
    simpa [η] using
      quadraticCharC_neg_one_eq_one_of_card_mod_four_one
        (F := F) hodd hqmod
  have hfib :=
    sum_over_squares_via_quadraticCharC
      (F := F) hodd
      (fun t : F => chi4 t * η (t - 1))
  calc
    (∑ x : F,
        quadraticCharC F ((x - 1) * x * (x + 1)))
        = ∑ x : F,
            (fun t : F => chi4 t * η (t - 1)) (x ^ 2) := by
              apply Finset.sum_congr rfl
              intro x hx
              have hchi4x : chi4 (x ^ 2) = η x := by
                have heval :=
                  congrArg
                    (fun χ : MulChar F ℂ => χ x) hchi4sq
                simpa [pow_two] using heval
              change
                quadraticCharC F ((x - 1) * x * (x + 1)) =
                  chi4 (x ^ 2) * η (x ^ 2 - 1)
              rw [hchi4x]
              change
                η ((x - 1) * x * (x + 1)) =
                  η x * η (x ^ 2 - 1)
              rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
              simp only [map_mul]
              ring
    _ = ∑ t : F,
          (1 + quadraticCharC F t) *
            (chi4 t * η (t - 1)) := by
          exact hfib
    _ = jacobiSum chi4 η +
          jacobiSum (chi4 * η) η := by
          rw [jacobiSum, jacobiSum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro t ht
          have hshift : η (t - 1) = η (1 - t) := by
            rw [show t - 1 = (-1 : F) * (1 - t) by ring]
            rw [map_mul, hηneg, one_mul]
          rw [hshift]
          change
            (1 + quadraticCharC F t) *
                (chi4 t * η (1 - t)) =
              chi4 t * η (1 - t) +
                (chi4 t * η t) * η (1 - t)
          simp [η]
          ring
    _ = jacobiSum chi4 (quadraticCharC F) +
          jacobiSum (chi4 * quadraticCharC F) (quadraticCharC F) := by
          simp [η]

end MagicSquares
