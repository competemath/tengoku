import Tengoku.Nlalib.NLAlib.Matrix.Basic.JacobiMinor
import Tengoku.Nlalib.NLAlib.Matrix.Inequalities.HadamardDeterminant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Singleton complement minors and inverse Hadamard

Jacobi's identity identifies inverse diagonal entries with deleted principal
minors. Hadamard on the inverse gives the local inequality underlying Szász,
with equality exactly for a diagonal matrix.
Source: Horn--Johnson (2013), Lemma 7.8.8 and Theorem 7.8.11;
supports `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For an invertible matrix, diagonal structure is preserved and reflected
by inversion. Horn--Johnson (2013), Section 0.8;
helper for the equality case in inverse Hadamard.
@isnad1 id=iff.1h2v.s5.5466938cc42b from=translated src=- shape=c7914c66 vocab=e3b05093
-/
theorem isDiag_inv_iff_of_isUnit {A : Matrix n n ℝ} (hA : IsUnit A) :
    A⁻¹.IsDiag ↔ A.IsDiag := by
  let : Invertible A := hA.invertible
  constructor
  · intro h
    rw [← Matrix.inv_inv_of_invertible A, ← h.diagonal_diag, Matrix.inv_diagonal]
    exact Matrix.isDiag_diagonal _
  · intro h
    rw [← h.diagonal_diag, Matrix.inv_diagonal]
    exact Matrix.isDiag_diagonal _

end NLAlib
