/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Entries are bounded by the spectral norm

`|A i j| ≤ ‖A‖₂` for a real matrix (`abs_apply_le_specNorm`): the entry is a coordinate of
`A *ᵥ eⱼ`, whose Euclidean norm is at most `‖A‖₂`.-/

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The norm of any entry of a real or complex matrix is bounded by its
spectral norm, on arbitrary finite index types.
@isnad1 id=le.0h6v.s5.c0dd739c5fe9 from=translated src=- shape=b13a09c4 vocab=62f3f980
-/
theorem norm_apply_le_specNorm {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) (i : m) (j : n) :
    ‖A i j‖ ≤ specNorm A := by
  let e : EuclideanSpace 𝕜 n := EuclideanSpace.single j 1
  let y : EuclideanSpace 𝕜 m := WithLp.toLp 2 (Matrix.mulVec A e.ofLp)
  have hcoord : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop : ‖y‖ ≤ specNorm A * ‖e‖ := Matrix.l2_opNorm_mulVec A e
  calc
    ‖A i j‖ = ‖y i‖ := by simp [y,e]
    _ ≤ ‖y‖ := hcoord
    _ ≤ specNorm A * ‖e‖ := hop
    _ = specNorm A := by simp [e]

open scoped Matrix.Norms.L2Operator in
/-- The absolute value of a real matrix entry is bounded by its spectral norm.
@isnad1 id=le.0h5v.s5.5c486ec0e319 from=translated src=- shape=eb1f2d35 vocab=b89412fa
-/
theorem abs_apply_le_specNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℝ) (i : m) (j : n) : |A i j| ≤ specNorm A := by
  simpa only [Real.norm_eq_abs] using norm_apply_le_specNorm A i j

end NLAlib
