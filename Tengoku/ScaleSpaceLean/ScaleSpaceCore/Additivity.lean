/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.Cascade
import Tengoku.Seed.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `lem:additivity`: the cascade, at the level of measures and of exponents

Home: line:lem:additivity

Blueprint: `blueprint/src/parts/05-cascade.tex`, `lem:additivity`.

Chapter 5 opens by transporting (A6) down two levels. `lem:convolution-representation` turned
the operators into measures — supplied here as the hypothesis `IsKernelFamily` — and
`Cascade` reads the cascade law off it as an identity of measures; the
transform turns convolution into multiplication, and `-log` turns multiplication into addition.
What comes out is a two-parameter family of exponents additive along the cascade, hence the
difference of the single one-parameter function `G(t, ω) = g_{0,t}(ω)`.

twin: `Hemigroup.CascadeCore.additivity`, bundled the same way so the blueprint node has one
Lean name for its ten clauses. The one place the two developments part company is the
positivity of the transform: on the half-line it is free (`laplace_pos_of_prob`), here it is
`lem:nonvanishing` and costs the whole of `Cascade`.

`G` is not given a name. The blueprint's `G(t,ω) := g_{0,t}(ω)` is written inline as
`exponent (μ 0 t) ω` throughout: it is an abbreviation in the text, and naming a function of a
hypothesised object in the `sorry`-free library would be vocabulary without a consumer.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Additivity.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## Elementary properties of the cosine transform

Four of the five this file proved — continuity, evenness, the value at `0` and the bound `≤ 1` —
were proved again in `Nonvanishing` for `lem:nonvanishing`, and the wave-1 merge
(2026-09-09) kept that copy and deleted these. Only the absolute-value form below is this file's
own.
-/

lemma abs_fourierCos_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (ω : ℝ) :
    |fourierCos ν ω| ≤ 1 := by
  calc |fourierCos ν ω| = ‖∫ x, Real.cos (ω * x) ∂ν‖ := by
        rw [fourierCos_apply, Real.norm_eq_abs]
    _ ≤ ∫ x, ‖Real.cos (ω * x)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ _, (1:ℝ) ∂ν :=
        integral_mono (integrable_cos_mul ν ω).norm (integrable_const 1)
          (fun x => by simpa using Real.abs_cos_le_one (ω * x))
    _ = 1 := by simp

/-! ## The exponents -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- **`g_{r,t} = g_{r,s} + g_{s,t}`.** Convolution becomes multiplication under the transform and
multiplication becomes addition under `-log`, which is legitimate exactly because the transform
of a kernel is strictly positive (`kernel_transform_pos`).-/
theorem exponent_add (hker : IsKernelFamily Fam.Φ μ) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hst : s ≤ t) (ω : ℝ) :
    exponent (μ r t) ω = exponent (μ r s) ω + exponent (μ s t) ω := by
  have h1 := kernel_transform_pos hker hr hrs ω
  have h2 := kernel_transform_pos hker (hr.trans hrs) hst ω
  simp only [exponent_apply, fourierCos_kernel_mul_comm hker hr hrs hst ω]
  rw [Real.log_mul h2.ne' h1.ne']
  ring

/-- **`G(t,·)` is continuous** — the continuity of a characteristic function.-/
theorem continuous_exponent (hker : IsKernelFamily Fam.Φ μ) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (exponent (μ 0 t)) := by
  haveI := hker.isProbability 0 t le_rfl ht
  exact ((continuous_fourierCos (μ 0 t)).log
    fun ω => (kernel_transform_pos hker le_rfl ht ω).ne').neg

end ScaleSpace
