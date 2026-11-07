/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.LinearAlgebra.Matrix.Permutation
import Tengoku.Seed.LinearAlgebra.UnitaryGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unitarity of permutation matrices

This file records that a complex permutation matrix belongs to the unitary group.
-/

open scoped Matrix

namespace Equiv.Perm

/-- A complex permutation matrix is unitary.
@isnad1 id=mem.0h2v.s6.b649f4ec5d28 from=translated src=- shape=5ea862ca vocab=3445821a
-/
theorem permMatrix_mem_unitaryGroup {n : Type*} [DecidableEq n] [Fintype n]
    (σ : Equiv.Perm n) :
    permMatrix ℂ σ ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

end Equiv.Perm
