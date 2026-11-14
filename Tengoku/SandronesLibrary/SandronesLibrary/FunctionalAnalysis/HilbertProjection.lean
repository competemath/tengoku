/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.QuotientSpace
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.InnerProduct
import Tengoku.Seed.Analysis.InnerProductSpace.Projection.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Orthogonal projection onto closed subspaces

In a Hilbert space every closed linear subspace admits an orthogonal projection.  Mathlib's
`Submodule.starProjection` is exactly the full-space projection used in textbooks; this file
records membership, orthogonality, and nearest-point characterizations.
-/

namespace SandronesLibrary.FunctionalAnalysis

open SandronesLibrary.Topology.NormedSpace

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BanachSpace E]

/-- A closed linear subspace of a Hilbert space admits an orthogonal projection.

> **Entry**: functional-analysis.hilbert.projection-/
theorem closedSubspace_hasOrthogonalProjection (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) : S.HasOrthogonalProjection := by
  let _ : IsClosed (S : Set E) := hS
  infer_instance

/-- The orthogonal projection of `x` belongs to the target subspace.-/
theorem closedSubspace_starProjection_mem (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) (x : E) : S.starProjection x ∈ S := by
  let _ : IsClosed (S : Set E) := hS
  exact S.starProjection_apply_mem x

/-- The residual after orthogonal projection belongs to the orthogonal complement.-/
theorem closedSubspace_sub_starProjection_mem_orthogonal (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) (x : E) : x - S.starProjection x ∈ Sᗮ := by
  let _ : IsClosed (S : Set E) := hS
  exact S.sub_starProjection_mem_orthogonal x

/-- The orthogonal projection is a nearest point of `x` in the closed subspace.-/
theorem closedSubspace_starProjection_minimal (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) (x : E) :
    ‖x - S.starProjection x‖ = ⨅ y : S, ‖x - y‖ := by
  let _ : IsClosed (S : Set E) := hS
  exact S.starProjection_minimal x

end SandronesLibrary.FunctionalAnalysis
