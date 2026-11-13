import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.FiniteAbsorption

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Simultaneous elimination of the outside diagonal blocks

Two square-zero shears suffice for the whole family. The orthogonality estimates
charge the square root of the number of blocks, rather than iterating a polynomial.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace NoEpsilon.Absorption

variable {ι n r : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]

variable (d : ι → Type*) [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

omit [DecidableEq ι] in
theorem outside_projection_norm_le (V : ∀ i, Matrix n (d i) ℂ)
    (hVV : ∀ i, (V i)ᴴ * V i = 1)
    (hOrth : ∀ i j, i ≠ j → (V i)ᴴ * V j = 0) :
    ‖∑ i, V i * (V i)ᴴ‖ ≤ 1 := by
  let E := ∑ i, V i * (V i)ᴴ
  have hE : Eᴴ = E := by simp only [E, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  have hEE : E * E = E := by
    dsimp [E]
    rw [Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_sum]
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (V i)ᴴ, hVV, Matrix.one_mul]
    · intro j _ hji
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (V i)ᴴ, hOrth i j hji.symm,
        Matrix.zero_mul, Matrix.mul_zero]
    · simp
  have hs := Matrix.l2_opNorm_conjTranspose_mul_self E
  rw [hE, hEE] at hs
  nlinarith [norm_nonneg E]

/-- The polynomial growth budget of two simultaneous shears.-/
noncomputable def simultaneousBudget (a : ℝ) (m : ℕ) : ℝ :=
  let u := 1 + a + Real.sqrt m
  let a₁ := a * u ^ 2
  a₁ * (1 + Real.sqrt m * a₁) ^ 2

end NoEpsilon.Absorption
