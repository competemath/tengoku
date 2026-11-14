/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.OpenMapping
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.ClosedGraph
import Tengoku.Seed.Analysis.Normed.Operator.Banach

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded inverse theorem

A bijective linear map is represented by `LinearEquiv`.  Between Banach spaces, continuity of the
forward map forces continuity of its algebraic inverse, which can then be bundled as a
`ContinuousLinearEquiv`.  No parallel inverse-operator structure is needed.
-/

namespace SandronesLibrary.FunctionalAnalysis

open SandronesLibrary.Topology.NormedSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedLinearSpace ℝ E] [NormedLinearSpace ℝ F]
variable [BanachSpace E] [BanachSpace F]

/-- **Bounded inverse theorem**: the inverse of a continuous linear equivalence between Banach
spaces is continuous.

The forward map is given as an algebraic `LinearEquiv`; continuity upgrades both directions.

> **Entry**: functional-analysis.inverse-operator-/
theorem linearEquiv_inverse_continuous (e : E ≃ₗ[ℝ] F) (he : Continuous e) :
    Continuous e.symm := by
  exact e.continuous_symm he

/-- A continuous algebraic linear equivalence between Banach spaces canonically upgrades to a
continuous linear equivalence with the same forward map.-/
theorem linearEquiv_upgrades_to_continuousLinearEquiv (e : E ≃ₗ[ℝ] F) (he : Continuous e) :
    ∃ eL : E ≃L[ℝ] F, ∀ x : E, eL x = e x := by
  exact ⟨e.toContinuousLinearEquivOfContinuous he, fun _ ↦ rfl⟩

/-- Quantitative bounded-inverse form: the inverse satisfies a global norm estimate.-/
theorem linearEquiv_inverse_exists_norm_bound (e : E ≃ₗ[ℝ] F) (he : Continuous e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : F, ‖e.symm y‖ ≤ C * ‖y‖ := by
  let eL : E ≃L[ℝ] F := e.toContinuousLinearEquivOfContinuous he
  refine ⟨‖(eL.symm : F →L[ℝ] E)‖, norm_nonneg _, fun y ↦ ?_⟩
  exact (eL.symm : F →L[ℝ] E).le_opNorm y

end SandronesLibrary.FunctionalAnalysis
