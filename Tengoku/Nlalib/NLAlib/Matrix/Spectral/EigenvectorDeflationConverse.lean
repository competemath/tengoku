import Tengoku.Nlalib.NLAlib.Matrix.Spectral.AdjugateRankOne
import Tengoku.Seed.LinearAlgebra.Eigenspace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# The converse to paired deflation and the eigenvalue adjugate

An isolated similarity coordinate gives a paired right column and inverse
row. At geometric multiplicity one the adjugate is their nonzero rank-one
outer product, even when the eigenvalue is defective.
Source: Horn–Johnson (2013), Theorems 1.4.7 and 1.4.12.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- An isolated row and column under an invertible similarity supply nonzero
right and left eigenvectors with pairing one. Source: Horn–Johnson (2013),
Theorem 1.4.7, converse; the left vector is the corresponding inverse row.
atlas: left-right-eigenvectors-/
theorem eigenpair_of_isolated_similarity
    (A S : Matrix n n K) (i : n) (μ : K) (hS : IsUnit S)
    (hcol : ∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0)
    (hrow : ∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) :
    Matrix.col S i ≠ 0 ∧ (fun j => S⁻¹ i j) ≠ 0 ∧
    (fun j => S⁻¹ i j) ⬝ᵥ Matrix.col S i = 1 ∧
    A *ᵥ Matrix.col S i = μ • Matrix.col S i ∧
    (fun j => S⁻¹ i j) ᵥ* A = μ • (fun j => S⁻¹ i j) := by
  let := hS.nonempty_invertible.some
  have hpair : (fun j => S⁻¹ i j) ⬝ᵥ Matrix.col S i = 1 := by
    change (S⁻¹ * S) i i = 1
    rw [Matrix.inv_mul_of_invertible]
    simp
  have hx : Matrix.col S i ≠ 0 := by intro h; simp [h] at hpair
  have hy : (fun j => S⁻¹ i j) ≠ 0 := by intro h; rw [h, zero_dotProduct] at hpair; exact zero_ne_one hpair
  refine ⟨hx, hy, hpair, ?_, ?_⟩
  · have hAS : A * S = S * (S⁻¹ * A * S) := by
      simp only [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
    funext j
    change (A * S) j i = μ * S j i
    rw [hAS, Matrix.mul_apply]
    simp only [hcol, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact mul_comm _ _
  · have hSA : S⁻¹ * A = (S⁻¹ * A * S) * S⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
    funext j
    change (S⁻¹ * A) i j = μ * S⁻¹ i j
    rw [hSA, Matrix.mul_apply]
    simp only [hrow, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end NLAlib
