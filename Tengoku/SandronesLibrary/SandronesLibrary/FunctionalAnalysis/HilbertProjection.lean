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

> **Entry**: functional-analysis.hilbert.projection
@isnad1 id=hasortho.1h2v.s6.641ad7d0563f from=translated src=- shape=84ecab0d vocab=40158e85
-/
theorem closedSubspace_hasOrthogonalProjection (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) : S.HasOrthogonalProjection := by
  let _ : IsClosed (S : Set E) := hS
  infer_instance

/-- The orthogonal projection of `x` belongs to the target subspace.
@isnad1 id=mem.1h3v.s8.2c929e32182b from=translated src=- shape=5d3c0945 vocab=b970ebb4
-/
theorem closedSubspace_starProjection_mem (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) (x : E) : S.starProjection x ∈ S := by
  let _ : IsClosed (S : Set E) := hS
  exact S.starProjection_apply_mem x

/-- The residual after orthogonal projection belongs to the orthogonal complement.
@isnad1 id=mem.1h3v.s8.3a1ddc2ad73d from=translated src=- shape=c6969070 vocab=7f361d62
-/
theorem closedSubspace_sub_starProjection_mem_orthogonal (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) (x : E) : x - S.starProjection x ∈ Sᗮ := by
  let _ : IsClosed (S : Set E) := hS
  exact S.sub_starProjection_mem_orthogonal x

/-- The orthogonal projection is a nearest point of `x` in the closed subspace.
@isnad1 id=eq.1h3v.s9.668d454284a9 from=translated src=- shape=3e06d642 vocab=fe741f09
-/
theorem closedSubspace_starProjection_minimal (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) (x : E) :
    ‖x - S.starProjection x‖ = ⨅ y : S, ‖x - y‖ := by
  let _ : IsClosed (S : Set E) := hS
  exact S.starProjection_minimal x

end SandronesLibrary.FunctionalAnalysis
