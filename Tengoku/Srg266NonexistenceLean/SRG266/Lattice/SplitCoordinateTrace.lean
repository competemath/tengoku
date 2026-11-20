/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

theorem sum_coordinate_eigenvalues_of_split
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : (ι → ℚ) →ₗ[ℚ] (κ → ℚ)) (g : (κ → ℚ) →ₗ[ℚ] (ι → ℚ))
    (hfg : f.comp g = LinearMap.id) (a : ι → ℚ)
    (ha : ∀ i, g (f (Pi.single i 1)) = a i • Pi.single i 1) :
    (∑ i, a i) = (Fintype.card κ : ℚ) := by
  have ht : LinearMap.trace ℚ (ι → ℚ) (g.comp f) = ∑ i, a i := by
    rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ ι)]
    simp [Matrix.trace, ha]
  have h := LinearMap.trace_comp_comm' f g
  rw [ht, hfg, LinearMap.trace_id] at h
  simpa using h

end SRG266.Lattice
