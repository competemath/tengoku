import Tengoku.Nlalib.NLAlib.RandomMatrix.Chaos.CoefficientRecursion
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic recursion of the actual chaos polynomial

Freezing the last coordinate group produces a linear matrix series. Its row,
column, and entry coefficient blocks are exactly the three lower-degree chaos
polynomials of the coefficient-recursion API.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NLAlib

variable {τ ι m n 𝕜 : Type*} [Fintype τ] [Fintype ι] [DecidableEq τ]
  [DecidableEq ι] [RCLike 𝕜]

private def appendTupleEquiv : ((τ ⊕ Unit) → ι) ≃ (τ → ι) × ι :=
  (Equiv.sumArrowEquivProdArrow τ Unit ι).trans
    ((Equiv.refl _).prodCongr (Equiv.funUnique Unit ι))

/-- The actual decoupled polynomial is a linear series in its final coordinate
group, with coefficients given by lower-degree decoupled polynomials.
@isnad1 id=eq.0h8v.s8.030e987bc514 from=translated src=- shape=6dcf76dd vocab=64b73d00
-/
theorem decoupledMatrixChaos_sum_recursion
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) (h : τ → ι → ℝ) (g : ι → ℝ) :
    decoupledMatrixChaos A (Sum.elim h (fun _ => g)) =
      ∑ j, g j • decoupledMatrixChaos (fun z => A (chaosAppendTuple z j)) h := by
  unfold decoupledMatrixChaos
  rw [← (appendTupleEquiv (τ := τ) (ι := ι)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ext a b
  have hu : (uniqueElim j : Unit → ι) = (fun _ => j) := by
    funext u
    cases u
    rfl
  simp [appendTupleEquiv, Equiv.sumArrowEquivProdArrow, Equiv.funUnique,
    Equiv.piUnique, chaosAppendTuple, Matrix.smul_apply, smul_smul, mul_comm, hu]

/-- Horizontal blocks commute entrywise with the lower-degree chaos polynomial.
@isnad1 id=eq.0h7v.s7.6ee4b2b6e10a from=translated src=- shape=1bea8e2a vocab=ccd956c6
-/
theorem coefficientRow_decoupledMatrixChaos
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) (h : τ → ι → ℝ) :
    coefficientRow (fun j => decoupledMatrixChaos (fun z => A (chaosAppendTuple z j)) h) =
      decoupledMatrixChaos (chaosRowCoefficients A) h := by
  ext a jb
  simp [coefficientRow, decoupledMatrixChaos, chaosRowCoefficients, Matrix.sum_apply]

/-- Vertical blocks commute entrywise with the lower-degree chaos polynomial.
@isnad1 id=eq.0h7v.s7.7381ac40e6b4 from=translated src=- shape=f7d3db33 vocab=b4af4fd1
-/
theorem coefficientColumn_decoupledMatrixChaos
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) (h : τ → ι → ℝ) :
    coefficientColumn (fun j => decoupledMatrixChaos (fun z => A (chaosAppendTuple z j)) h) =
      decoupledMatrixChaos (chaosColumnCoefficients A) h := by
  ext ia b
  simp [coefficientColumn, decoupledMatrixChaos, chaosColumnCoefficients, Matrix.sum_apply]

/-- Entry-vectorization blocks commute with the lower-degree chaos polynomial.
@isnad1 id=eq.0h7v.s7.20b8325fc5de from=translated src=- shape=eee4aba7 vocab=ec3cd86a
-/
theorem coefficientEntryRows_decoupledMatrixChaos
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) (h : τ → ι → ℝ) :
    coefficientEntryRows (fun j => decoupledMatrixChaos (fun z => A (chaosAppendTuple z j)) h) =
      decoupledMatrixChaos (chaosEntryCoefficients A) h := by
  ext j ab
  simp [coefficientEntryRows, decoupledMatrixChaos, chaosEntryCoefficients, Matrix.sum_apply]

end NLAlib
