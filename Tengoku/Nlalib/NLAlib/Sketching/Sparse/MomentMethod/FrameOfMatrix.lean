/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.MomentMethod.GramTail
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From an orthonormal-column matrix to the Parseval-frame representation

The paper starts with an `n × d` matrix `U` satisfying `UᵀU = I`.  The
operator proof uses its rows as a Parseval frame.  This file makes that change
of representation literal and reversible at the matrix level.
-/

namespace NLAlib.SparseSketch

noncomputable section

/-- The Euclidean row family of a real matrix.

Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def matrixRows {n d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ) : Fin n → EVec d :=
  fun i ↦ WithLp.toLp 2 (fun a ↦ U i a)

/-- The Euclidean matrix-row family reads the original matrix entries.
Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h5v.s5.250410312821 from=translated src=- shape=7d6a171f vocab=b3b9ec38
-/
@[simp] theorem matrixRows_apply {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) (a : Fin d) :
    matrixRows U i a = U i a := rfl

/-- Converting matrix rows back to their coordinate matrix recovers the input.
Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s4.b0827eacfabb from=translated src=- shape=d5e33072 vocab=b420ef13
-/
@[simp] theorem rowMatrix_matrixRows {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ) :
    rowMatrix (matrixRows U) = U := by
  rfl

/-- An orthonormal-column matrix, represented as the exact Parseval structure
used by the sparse-Fock proof.

Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def frameOfMatrix {n d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) : Frame n d where
  u := matrixRows U
  parseval := by
    apply (parseval_iff_transpose_mul (matrixRows U)).2
    simpa using hU

/-- The Parseval frame of an orthonormal-column matrix consists of its Euclidean rows.
Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h5v.s7.54524e7d751f from=translated src=- shape=abda2615 vocab=cfc848af
-/
@[simp] theorem frameOfMatrix_u {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ))
    (i : Fin n) (a : Fin d) :
    (frameOfMatrix U hU).u i a = U i a := rfl

/-- The coordinate row matrix of the constructed Parseval frame recovers the input.
Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h3v.s6.57b8a1647003 from=translated src=- shape=b510cbbc vocab=30780e64
-/
@[simp] theorem frameOfMatrix_rowMatrix {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) :
    rowMatrix (frameOfMatrix U hU).u = U := by
  rfl

/-- For the frame of an orthonormal-column matrix `U`, the embedded Gram matrix of any sketch
`S` is the paper's literal `Uᵀ (SᵀS) U`.

Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h5v.s7.142a4735afaa from=translated src=- shape=75a2ad06 vocab=345c86fa
-/
@[simp] theorem embeddedGram_frameOfMatrix {k : Type*} [Fintype k] {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ))
    (S : Matrix k (Fin n) ℝ) :
    embeddedGram (frameOfMatrix U hU) S =
      U.transpose * (sketchGram S * U) := by
  simp [embeddedGram]

/-- Consequently the formal Gram error is exactly the displayed matrix in the
main probability event.

Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h5v.s7.6663895cbe07 from=translated src=- shape=5f05199c vocab=295a3622
-/
@[simp] theorem gramError_frameOfMatrix {k : Type*} [Fintype k] {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ))
    (S : Matrix k (Fin n) ℝ) :
    gramError (frameOfMatrix U hU) S =
      U.transpose * (sketchGram S * U) - 1 := by
  simp [gramError]

end

end NLAlib.SparseSketch
