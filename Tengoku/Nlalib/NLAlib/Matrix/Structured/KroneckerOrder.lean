import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.LinearAlgebra.Matrix.Kronecker

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Loewner order under Kronecker products

Positive tensor factors preserve the finite matrix order. These order
bridges are shared by tensor compressions and matrix-valued polynomial models.
-/

noncomputable section
open scoped MatrixOrder Kronecker ComplexOrder
namespace Matrix
variable {𝕜 m n : Type*} [RCLike 𝕜]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Tensoring on the right by a PSD matrix preserves Loewner order.
@isnad1 id=le.2h6v.s7.f7a5181ba8d0 from=translated src=- shape=b05cf5c3 vocab=35ca99ac
-/
theorem kronecker_le_kronecker_right {A B : Matrix m m 𝕜} {C : Matrix n n 𝕜}
    (hAB : A ≤ B) (hC : C.PosSemidef) : A ⊗ₖ C ≤ B ⊗ₖ C := by
  apply Matrix.le_iff.mpr
  have he : B ⊗ₖ C - A ⊗ₖ C = (B - A) ⊗ₖ C := by
    ext a b
    simp [Matrix.kronecker_apply, sub_mul]
  rw [he]
  exact (Matrix.le_iff.mp hAB).kronecker hC

/-- Tensoring on the left by a PSD matrix preserves Loewner order.
@isnad1 id=le.2h6v.s7.265c5a8ffa43 from=translated src=- shape=64dce9fa vocab=35ca99ac
-/
theorem kronecker_le_kronecker_left {A B : Matrix n n 𝕜} {C : Matrix m m 𝕜}
    (hAB : A ≤ B) (hC : C.PosSemidef) : C ⊗ₖ A ≤ C ⊗ₖ B := by
  apply Matrix.le_iff.mpr
  have he : C ⊗ₖ B - C ⊗ₖ A = C ⊗ₖ (B - A) := by
    ext a b
    simp [Matrix.kronecker_apply, mul_sub]
  rw [he]
  exact hC.kronecker (Matrix.le_iff.mp hAB)

/-- Rectangular congruence preserves the Loewner order.
@isnad1 id=le.1h6v.s8.9d3b1d6f6a94 from=translated src=- shape=50c2468a vocab=c900842a
-/
theorem conjTranspose_mul_le_conjTranspose_mul {A B : Matrix m m 𝕜}
    (hAB : A ≤ B) (C : Matrix m n 𝕜) : Cᴴ * A * C ≤ Cᴴ * B * C := by
  apply Matrix.le_iff.mpr
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same C

/-- Multiplication by a nonnegative real scalar preserves Loewner order.
This uses the PSD cone directly rather than a pointwise matrix order.
@isnad1 id=le.2h5v.s7.8c9939940f4c from=translated src=- shape=1b237707 vocab=0b869bd1
-/
theorem real_smul_le_real_smul {A B : Matrix n n 𝕜} (hAB : A ≤ B)
    {r : ℝ} (hr : 0 ≤ r) : r • A ≤ r • B := by
  apply Matrix.le_iff.mpr
  rw [← smul_sub]
  exact (Matrix.le_iff.mp hAB).smul hr

end Matrix
