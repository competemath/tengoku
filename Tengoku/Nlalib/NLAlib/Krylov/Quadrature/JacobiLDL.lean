import Tengoku.Nlalib.NLAlib.Matrix.Structured.JacobiLDL
import Tengoku.Nlalib.NLAlib.Krylov.Quadrature.JacobiFraction
import Tengoku.Nlalib.NLAlib.Matrix.Subspaces.OrthogonalProducts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # LDL pivots of the actual Lanczos compression

An SPD matrix has an SPD compression by the actual orthonormal Lanczos basis.
Thus the symmetric Jacobi factorization and its positive scalar pivots apply
without additional pivot assumptions and with arbitrary off-diagonal signs.
Source: Gautschi (2004), Theorem 1.33; operator derivations AQ15.
-/

noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib.LanczosDecomp
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- Positive definiteness passes to the actual Lanczos compression, including
the empty compression, by injectivity of its orthonormal columns.
@isnad1 id=posdef.1h5v.s5.0a72c3e97427 from=translated src=- shape=a58b0a64 vocab=97edd786
-/
theorem posDef_T (D : LanczosDecomp A b q) (hA : A.PosDef) : D.T.PosDef := by
  have hQ : Function.Injective D.Q.mulVec :=
    Matrix.mulVec_injective_iff.mpr D.hasOrthonormalCols.linearIndependent_col
  simpa only [T, ArnoldiDecomp.H_def, Matrix.conjTranspose_eq_transpose_of_trivial]
    using hA.conjTranspose_mul_mul_same hQ

/-- Every scalar LDL pivot of an actual SPD Lanczos compression is positive.
The signed off-diagonal is squared in the recurrence.
atlas: kernel-polynomials-christoffel (partial)
@isnad1 id=lt.2h6v.s6.a23e49c8c632 from=translated src=- shape=89ab0340 vocab=4172af0f
-/
theorem jacobiLDLPivot_pos (D : LanczosDecomp A b q) (hA : A.PosDef)
    {k : ℕ} (hk : k < q) : 0 < jacobiLDLPivot D.alpha D.beta k := by
  have hT := D.posDef_T hA
  rw [D.T_eq_jacobiMatrix hA.isHermitian] at hT
  exact jacobiLDLPivot_pos_of_posDef hT hk

/-- The actual symmetric SPD Lanczos Jacobi matrix equals its explicit
positive-pivot unit lower bidiagonal LDL transpose product.
atlas: kernel-polynomials-christoffel (partial)
@isnad1 id=eq.1h5v.s7.0fdeda5a2a15 from=translated src=- shape=5a20bd69 vocab=5a189baa
-/
theorem T_eq_ldl (D : LanczosDecomp A b q) (hA : A.PosDef) :
    D.T = jacobiLDLLower D.alpha D.beta q *
      diagonal (fun i : Fin q => jacobiLDLPivot D.alpha D.beta i.val) *
      (jacobiLDLLower D.alpha D.beta q)ᵀ := by
  rw [D.T_eq_jacobiMatrix hA.isHermitian]
  apply jacobiMatrix_eq_ldl_of_posDef
  rw [← D.T_eq_jacobiMatrix hA.isHermitian]
  exact D.posDef_T hA

end NLAlib.LanczosDecomp
