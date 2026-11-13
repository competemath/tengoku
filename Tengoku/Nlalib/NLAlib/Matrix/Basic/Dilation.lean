import Tengoku.Seed.Data.Matrix.Block
import Tengoku.Seed.LinearAlgebra.Matrix.Hermitian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Hermitian dilation

The Hermitian dilation `[0 A; Aᴴ 0]` of a rectangular matrix over any ring with a star (complex
matrices for matrix concentration, real matrices, where `Aᴴ = Aᵀ`, for the Mirsky and Lidskii
arguments), with its immediate API: it is Hermitian (`isHermitian_dilation`) and additive
(`dilation_add`).

Tropp 2015, §2.1.17. Atlas: `hermitian-dilation`.
-/

namespace NLAlib

/-- The Hermitian dilation `fromBlocks 0 A Aᴴ 0` of a rectangular matrix `A`. Tropp 2015,
Def. 2.1.5; over `ℝ` this is the symmetric dilation `[0 A; Aᵀ 0]` of Bhatia 1997, Section III.4.
Stated over any `α` with `0` and `star` (generalised from `ℂ`).
atlas: hermitian-dilation-/
def dilation {α : Type*} [Zero α] [Star α] {m n : Type*} (A : Matrix m n α) :
    Matrix (Sum m n) (Sum m n) α := Matrix.fromBlocks 0 A A.conjTranspose 0

/-- The dilation is Hermitian (symmetric over `ℝ`). Bhatia 1997, Section III.4;
Tropp 2015, §2.1.16.
@isnad1 id=ishermit.0h4v.s5.7ad511457cab from=translated src=- shape=24a878b4 vocab=2596d3ab
-/
theorem isHermitian_dilation {α : Type*} [AddMonoid α] [StarAddMonoid α] {m n : Type*}
    (A : Matrix m n α) : (dilation A).IsHermitian := by
  simp [dilation, Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]

/-- The dilation is additive. Bhatia 1997, Section III.4.
@isnad1 id=eq.0h5v.s7.33872fd7822a from=translated src=- shape=8bb341b0 vocab=baa5fd72
-/
theorem dilation_add {α : Type*} [AddMonoid α] [StarAddMonoid α] {m n : Type*}
    (A B : Matrix m n α) : dilation (A + B) = dilation A + dilation B := by
  simp [dilation, Matrix.fromBlocks_add]

end NLAlib
