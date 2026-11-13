import Tengoku.Seed.Analysis.Matrix.PosDef

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gram factors with diagonal row Gram matrices

A positive matrix has a square row factor whose row Gram matrix is
its diagonal eigenvalue list and whose column Gram is the matrix itself.
This is a convenient common realization for spectral-sum inequalities.
Horn--Johnson, Matrix Analysis, Section 7.3.
-/

noncomputable section
open Matrix
open scoped ComplexOrder
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The spectral square-row Gram factor of a positive semidefinite matrix.-/
def spectralGramRows {A : Matrix n n 𝕜} (hA : A.PosSemidef) : Matrix n n 𝕜 :=
  diagonal (fun i => (Real.sqrt (hA.isHermitian.eigenvalues i) : 𝕜)) *
    (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜).conjTranspose

private theorem diagonal_sqrt_gram {ev : n → ℝ} (hev : ∀ i, 0 ≤ ev i) :
    let D := diagonal (fun i => (Real.sqrt (ev i) : 𝕜))
    D.conjTranspose=D ∧ D*D=diagonal (fun i => (ev i : 𝕜)) := by
  dsimp
  constructor
  · ext i j
    by_cases hij : i=j
    · subst j; simp [Matrix.conjTranspose_apply]
    · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hev i)]

/-- The column Gram of the spectral row factor is the original matrix.
@isnad1 id=eq.1h3v.s7.ba5a4f8d87db from=translated src=- shape=06fb6be0 vocab=bf1f1dac
-/
theorem spectralGramRows_adjoint_mul {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (spectralGramRows hA).conjTranspose*spectralGramRows hA=A := by
  obtain ⟨hD, hDD⟩ := diagonal_sqrt_gram (𝕜 := 𝕜) hA.eigenvalues_nonneg
  rw [spectralGramRows, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hD, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), hDD]
  simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def, Matrix.mul_assoc] using hA.isHermitian.spectral_theorem.symm

/-- The row Gram of the spectral row factor is the diagonal eigenvalue list.
@isnad1 id=eq.1h3v.s7.005bdfaf3164 from=translated src=- shape=6c9a03f2 vocab=3e1e70a2
-/
theorem spectralGramRows_mul_adjoint {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    spectralGramRows hA*(spectralGramRows hA).conjTranspose=
      diagonal (fun i => (hA.isHermitian.eigenvalues i : 𝕜)) := by
  obtain ⟨hD, hDD⟩ := diagonal_sqrt_gram (𝕜 := 𝕜) hA.eigenvalues_nonneg
  have hU : (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜).conjTranspose *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜)=1 := Unitary.coe_star_mul_self _
  rw [spectralGramRows, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hD, Matrix.mul_assoc, ← Matrix.mul_assoc (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜).conjTranspose
      (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) _, hU, Matrix.one_mul]
  exact hDD

end NLAlib
