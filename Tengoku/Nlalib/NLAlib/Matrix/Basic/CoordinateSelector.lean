import Tengoku.Seed.Analysis.RCLike.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Hermitian
import Tengoku.Seed.Data.Matrix.Mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Coordinate projections and padded row restriction

The same diagonal selector represents a coordinate projection and selects
rows while retaining the ambient labels. This is the existing Schur–Horn
selector, moved to the matrix basics and generalized to both scalar fields.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [DecidableEq n]

/-- The diagonal projection onto a finite set of coordinate labels.-/
def coordinateSelector (S : Finset n) : Matrix n n 𝕜 :=
  Matrix.diagonal (fun i => if i ∈ S then 1 else 0)

/-- A coordinate selector is Hermitian over either scalar field.
@isnad1 id=ishermit.0h3v.s6.576be19a287c from=translated src=- shape=7f8728ba vocab=6bf1e53b
-/
theorem coordinateSelector_isHermitian (S : Finset n) :
    (coordinateSelector S : Matrix n n 𝕜).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  change star (fun i => if i ∈ S then (1 : 𝕜) else 0) = _
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

variable [Fintype n]

/-- Multiplication by a coordinate selector retains the selected rows and
sets all other rows to zero.
@isnad1 id=eq.0h7v.s7.8e38e06d702e from=translated src=- shape=a5578464 vocab=0e1e6085
-/
theorem coordinateSelector_mul_apply (S : Finset n) (X : Matrix n d 𝕜) (i : n) (j : d) :
    ((coordinateSelector S : Matrix n n 𝕜) * X) i j = if i ∈ S then X i j else 0 := by
  rw [coordinateSelector, Matrix.diagonal_mul]
  split_ifs <;> simp

/-- Coordinate restriction is an idempotent projection.
@isnad1 id=eq.0h3v.s6.dd4bec7b9b42 from=translated src=- shape=1eb0227d vocab=9c9087e4
-/
theorem coordinateSelector_mul_self (S : Finset n) :
    (coordinateSelector S : Matrix n n 𝕜) * coordinateSelector S = coordinateSelector S := by
  ext i j
  rw [coordinateSelector_mul_apply]
  by_cases hi : i ∈ S
  · simp [hi]
  · by_cases hij : i = j
    · subst j; simp [coordinateSelector, hi]
    · simp [coordinateSelector, hij]

/-- Selecting every coordinate leaves a matrix unchanged.
@isnad1 id=eq.0h2v.s6.f1581a9c4962 from=translated src=- shape=756269af vocab=7fa688c2
-/
@[simp] theorem coordinateSelector_univ :
    coordinateSelector (Finset.univ : Finset n) = (1 : Matrix n n 𝕜) := by
  simp [coordinateSelector]

/-- Complementary coordinate selectors are exactly the residual projection.
@isnad1 id=eq.0h3v.s7.09f5947ce63c from=translated src=- shape=e7a46945 vocab=21ed87b0
-/
theorem coordinateSelector_compl (S : Finset n) :
    (coordinateSelector Sᶜ : Matrix n n 𝕜) = 1 - coordinateSelector S := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S <;> simp [coordinateSelector, hi]
  · simp [coordinateSelector, hij]

end NLAlib
