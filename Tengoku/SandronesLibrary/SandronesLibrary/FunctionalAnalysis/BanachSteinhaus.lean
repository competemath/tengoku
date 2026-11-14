/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.Baire
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.OperatorSpace
import Tengoku.Seed.Analysis.Normed.Operator.BanachSteinhaus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Banach–Steinhaus theorem

Pointwise boundedness is written with its textbook quantifiers, while the operator family uses
Mathlib's `ContinuousLinearMap` directly.  The standard uniform boundedness theorem then supplies
one bound for all operator norms.
-/

namespace SandronesLibrary.FunctionalAnalysis

open SandronesLibrary.Topology.NormedSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedLinearSpace ℝ E] [NormedLinearSpace ℝ F] [BanachSpace E]

/-- **Banach–Steinhaus uniform boundedness principle**: a pointwise bounded family of continuous
linear maps on a Banach space has uniformly bounded operator norms.

> **Entry**: functional-analysis.banach-steinhaus
@isnad1 id=ex.1h4v.s8.4a828c5d22a4 from=translated src=- shape=59d6efe2 vocab=fefdf5e0
-/
theorem uniform_operatorNorm_bound_of_pointwise_bounded {ι : Type*} {g : ι → E →L[ℝ] F}
    (hPointwise : ∀ x : E, ∃ C : ℝ, ∀ i : ι, ‖g i x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ι, ‖g i‖ ≤ C := by
  rcases banach_steinhaus hPointwise with ⟨C, hC⟩
  exact ⟨max C 0, le_max_right C 0, fun i ↦ (hC i).trans (le_max_left C 0)⟩

/-- Pointwise consequence with the same uniform constant: every operator in the family satisfies
`‖gᵢ x‖ ≤ C ‖x‖`.
@isnad1 id=ex.1h4v.s8.d2139ed85de9 from=translated src=- shape=8f412887 vocab=8f4768ca
-/
theorem uniform_apply_bound_of_pointwise_bounded {ι : Type*} {g : ι → E →L[ℝ] F}
    (hPointwise : ∀ x : E, ∃ C : ℝ, ∀ i : ι, ‖g i x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ι, ∀ x : E, ‖g i x‖ ≤ C * ‖x‖ := by
  rcases uniform_operatorNorm_bound_of_pointwise_bounded hPointwise with ⟨C, hC, hnorm⟩
  refine ⟨C, hC, fun i x ↦ (g i).le_opNorm x |>.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (hnorm i) (norm_nonneg x)

end SandronesLibrary.FunctionalAnalysis
