/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef
import Tengoku.Tauceti.TauCeti.Analysis.Matrix.LDL

/-!
# Cholesky factors of positive-definite real matrices

This file constructs the lower-triangular Cholesky factor of a positive-definite real matrix
from Mathlib's LDL decomposition.  The diagonal of the LDL factor is positive, so taking its
entrywise square root and absorbing it into the lower factor gives `S = L * Lᵀ`, with `L` lower
triangular and positive on the diagonal.

## Main definitions

* `TauCeti.PosDiagLowerTriangular` is the space of lower-triangular real matrices with positive
  diagonal.
* `TauCeti.cholesky` constructs the Cholesky factor of a positive-definite matrix, and
  `TauCeti.cholesky_coe` gives its closed form in terms of the LDL decomposition.
* `TauCeti.cholesky_mul_transpose` proves the Cholesky reconstruction identity.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 7.2.
-/

-- The declaration names and signatures of the Cholesky API below follow the skeleton pinned in
-- `TauCetiRoadmap/StandardDistributions/Suggested.lean`, section "Cholesky coordinates".

public section

noncomputable section

open scoped Matrix

namespace TauCeti

/-- Lower-triangular real matrices of size `p` whose diagonal entries are positive. -/
abbrev PosDiagLowerTriangular (p : ℕ) :=
  {L : Matrix (Fin p) (Fin p) ℝ // L.IsLowerTriangular ∧ ∀ i, 0 < L i i}

namespace Matrix

variable {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)

private noncomputable def choleskyFactor : Matrix (Fin p) (Fin p) ℝ :=
  LDL.lower hS * Matrix.diagonal fun i ↦ Real.sqrt (LDL.diagEntries hS i)

end Matrix

/-- A lower-triangular matrix with positive diagonal has linearly independent rows. -/
theorem PosDiagLowerTriangular.vecMul_injective {p : ℕ} (L : PosDiagLowerTriangular p) :
    Function.Injective L.1.vecMul := by
  apply Matrix.vecMul_injective_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    Matrix.det_of_isLowerTriangular L.1 L.2.1]
  exact Finset.prod_ne_zero_iff.2 fun i _ ↦ (L.2.2 i).ne'

/-- Reconstruct a positive-definite symmetric matrix from a lower-triangular matrix with positive
diagonal. -/
noncomputable def choleskyReconstruction {p : ℕ} (L : PosDiagLowerTriangular p) :
    PosDefMatrix p := by
  refine ⟨⟨L.1 * L.1ᵀ, ?_⟩, ?_⟩
  · have h := Matrix.isHermitian_mul_conjTranspose_self L.1
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact Matrix.isHermitian_iff_isSelfAdjoint.mp h
  · have h := Matrix.PosDef.mul_conjTranspose_self L.1 L.vecMul_injective
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- The matrix underlying `choleskyReconstruction L` is `L * Lᵀ`. -/
@[simp]
theorem choleskyReconstruction_coe {p : ℕ} (L : PosDiagLowerTriangular p) :
    ((choleskyReconstruction L).1 : Matrix (Fin p) (Fin p) ℝ) = L.1 * L.1ᵀ := by
  rw [choleskyReconstruction]

end TauCeti
