/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Basic
public import Tengoku.Seed.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real Grassmannians as spaces of orthogonal projections

Directions are k-dimensional subspaces. The topology is induced by the operator
norm topology on their orthogonal projections, and the measurable space is Borel.
-/

@[expose] public section

namespace NKBesicovitch

/-- The real Grassmannian of k-dimensional subspaces of Euclidean n-space.-/
def Grassmannian (n k : ℕ) := {V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) // Module.finrank ℝ V = k}

namespace Grassmannian

variable {n k : ℕ}

/-- The orthogonal projection onto a direction, viewed as an ambient operator.-/
noncomputable def projection (V : Grassmannian n k) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  V.val.starProjection

noncomputable instance : TopologicalSpace (Grassmannian n k) :=
  TopologicalSpace.induced projection inferInstance

noncomputable instance : MeasurableSpace (Grassmannian n k) := borel (Grassmannian n k)

/--
@isnad1 id=injectiv.0h2v.s8.f63ab82928d1 from=translated src=- shape=e39008af vocab=108d8bb9
-/
theorem projection_injective : Function.Injective (projection (n := n) (k := k)) := by
  intro V W h
  apply Subtype.ext
  have hr := congrArg (fun p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) ↦
    LinearMap.range p.toLinearMap) h
  simpa [projection, Submodule.range_starProjection] using hr

end Grassmannian

end NKBesicovitch
