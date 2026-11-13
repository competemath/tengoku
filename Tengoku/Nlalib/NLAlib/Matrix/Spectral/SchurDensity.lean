import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SeparableCharpolyDensity
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SchurTriangularization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Dense distinct characteristic-root lists over the real and complex fields

The separability density theorem yields injective complex eigenvalue
lists, with real matrices perturbed within the real matrix space.
Source: Horn–Johnson (2013), §2.3.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex matrices admitting a complete list of pairwise distinct
characteristic eigenvalues are dense. Source: Horn–Johnson (2013), §2.3;
the characteristic factorization explicitly certifies multiplicities.
atlas: schur-triangularization
@isnad1 id=dense.0h1v.s7.308af0dca6d6 from=translated src=- shape=8d7b96a4 vocab=0b320c64
-/
theorem dense_exists_injective_charpoly_factors_complex :
    Dense {A : Matrix n n ℂ | ∃ d : n → ℂ, Function.Injective d ∧
      A.charpoly = ∏ i, (X - C (d i))} := by
  classical
  apply (dense_separable_charpoly (n := n) (K := ℂ)).mono
  intro A hA
  obtain ⟨U, T, _, _, hchar⟩ := exists_unitary_schur_triangularization A (Fintype.equivFin n).symm
  refine ⟨fun i => T i i, ?_, hchar⟩
  apply Polynomial.separable_prod_X_sub_C_iff.mp
  rw [← hchar]
  exact hA

/-- Real matrices admitting a complete list of pairwise distinct complex
characteristic eigenvalues are dense among real matrices.
Horn–Johnson (2013), §2.3; complexification records possible nonreal conjugate
pairs and imposes no real-spectrum restriction.
atlas: schur-triangularization
@isnad1 id=dense.0h1v.s7.7284e9788b9f from=translated src=- shape=e1a6b20c vocab=60395e5d
-/
theorem dense_exists_injective_charpoly_factors_real :
    Dense {A : Matrix n n ℝ | ∃ d : n → ℂ, Function.Injective d ∧
      (A.map Complex.ofReal).charpoly = ∏ i, (X - C (d i))} := by
  classical
  apply (dense_separable_charpoly (n := n) (K := ℝ)).mono
  intro A hA
  have hcharMap : (A.map Complex.ofReal).charpoly = Polynomial.map Complex.ofRealHom A.charpoly :=
    Matrix.charpoly_map A Complex.ofRealHom
  have hsep : (A.map Complex.ofReal).charpoly.Separable := by
    rw [hcharMap]
    exact hA.map
  obtain ⟨U, T, _, _, hchar⟩ := exists_unitary_schur_triangularization
    (A.map Complex.ofReal) (Fintype.equivFin n).symm
  refine ⟨fun i => T i i, ?_, hchar⟩
  apply Polynomial.separable_prod_X_sub_C_iff.mp
  rw [← hchar]
  exact hsep

end NLAlib
