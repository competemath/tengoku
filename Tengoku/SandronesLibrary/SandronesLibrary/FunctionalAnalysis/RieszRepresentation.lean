/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.HilbertProjection
import Tengoku.Seed.Analysis.InnerProductSpace.Dual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fréchet–Riesz representation theorem

The continuous dual of a real Hilbert space is represented directly by `E →L[ℝ] ℝ`.  Mathlib's
`InnerProductSpace.toDual` is the isometric equivalence sending a vector `y` to the functional
`x ↦ ⟪y, x⟫`; this file exposes existence, uniqueness, and norm preservation in textbook form.
-/

namespace SandronesLibrary.FunctionalAnalysis

open SandronesLibrary.Topology.NormedSpace

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BanachSpace E]

/-- **Fréchet–Riesz representation theorem**: every continuous linear functional on a real
Hilbert space is inner product with a unique representing vector.

> **Entry**: functional-analysis.hilbert.riesz-/
theorem existsUnique_inner_right_eq_continuousLinearFunctional (ℓ : E →L[ℝ] ℝ) :
    ∃! y : E, ∀ x : E, inner ℝ y x = ℓ x := by
  let y : E := (InnerProductSpace.toDual ℝ E).symm ℓ
  refine ⟨y, fun x ↦ InnerProductSpace.toDual_symm_apply, ?_⟩
  intro z hz
  apply (InnerProductSpace.toDual ℝ E).injective
  apply ContinuousLinearMap.ext
  intro x
  rw [InnerProductSpace.toDual_apply_apply, hz x,
    InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_symm_apply]

/-- The canonical representing vector supplied by `toDual.symm` satisfies the representation
identity.-/
theorem rieszRepresentative_inner (ℓ : E →L[ℝ] ℝ) (x : E) :
    inner ℝ ((InnerProductSpace.toDual ℝ E).symm ℓ) x = ℓ x := by
  exact InnerProductSpace.toDual_symm_apply

/-- The Riesz representing vector has the same norm as the continuous linear functional.-/
theorem norm_rieszRepresentative (ℓ : E →L[ℝ] ℝ) :
    ‖(InnerProductSpace.toDual ℝ E).symm ℓ‖ = ‖ℓ‖ := by
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map ℓ

end SandronesLibrary.FunctionalAnalysis
