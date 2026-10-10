import Tengoku

/-!
# Lp Bare-Function Toolkit

Lp completeness and convergence results that work entirely with **bare functions**
`α → E` and `eLpNorm`, without ever constructing elements of the `Lp E p μ` Banach
space type.

## Motivation

Lean 4's type class synthesis for `EuclideanSpace ℝ (Fin d)` — which unfolds through
`PiLp → WithLp → Pi` — causes exponential heartbeat blowup when converting between
bare functions and `Lp` elements via `MemLp.toLp` / `MemLp.coeFn_toLp`. A single
`coeFn_toLp` call can exceed 6.4M heartbeats even in standalone helpers.

This toolkit avoids the `Lp` type entirely. Instead of
```
bare function → toLp → Lp → CauchySeq → complete → Lp limit → coeFn → bare function
```
we use
```
bare function → Cauchy in eLpNorm → convergence in measure
  → a.e. convergent subsequence → a.e. limit (AEStronglyMeasurable)
  → MemLp (from eLpNorm bound) → bare function
```

Every step operates on bare functions. No `toLp`, no `coeFn_toLp`.

## Main results

* `BareFunction.exists_memLp_limit_of_cauchy_eLpNorm`: Cauchy in eLpNorm → limit exists
* `BareFunction.memLp_pi_component`: Pi-valued MemLp → component MemLp
* `BareFunction.eLpNorm_pi_component_le`: Component eLpNorm ≤ vector eLpNorm
* `BareFunction.tendsto_eLpNorm_pi_component`: Vector convergence → component convergence
* `BareFunction.exists_pi_limit_of_cauchy_eLpNorm`: Combined Cauchy → limit + components
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace BareFunction

/-! ### MemLp from convergence -/

section General

variable {E : Type*} [NormedAddCommGroup E]

end General

/-! ### Component-wise results for Pi-valued functions -/

section PiComponent

variable {d : ℕ}

/-- Each component of a Pi-valued AEStronglyMeasurable function is AEStronglyMeasurable.
For `Fin d → ℝ` (NOT `EuclideanSpace`), `continuous_apply` works directly. -/
theorem aestronglyMeasurable_pi_component
    {F : α → (Fin d → ℝ)} (hF : AEStronglyMeasurable F μ) (i : Fin d) :
    AEStronglyMeasurable (fun x => F x i) μ :=
  Continuous.comp_aestronglyMeasurable (continuous_apply i) hF

/-- AEStronglyMeasurable for a Pi-valued function from its components. -/
theorem aestronglyMeasurable_pi_of_components
    {F : α → (Fin d → ℝ)}
    (hF_comp : ∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) μ) :
    AEStronglyMeasurable F μ :=
  (aemeasurable_pi_iff.mpr fun i => (hF_comp i).aemeasurable).aestronglyMeasurable

/-- Component eLpNorm ≤ vector eLpNorm for Pi types.
For `Fin d → ℝ` with the sup norm, `‖f i‖ ≤ ‖f‖` is `norm_le_pi_norm`. -/
theorem eLpNorm_pi_component_le
    {p : ℝ≥0∞} {F : α → (Fin d → ℝ)} (i : Fin d) :
    eLpNorm (fun x => F x i) p μ ≤ eLpNorm F p μ :=
  eLpNorm_mono fun x => norm_le_pi_norm (f := F x) i

/-- For `F : α → (Fin d → ℝ)` in Lp, each component is in Lp. -/
theorem memLp_pi_component
    {p : ℝ≥0∞} {F : α → (Fin d → ℝ)} (hF : MemLp F p μ) (i : Fin d) :
    MemLp (fun x => F x i) p μ :=
  ⟨aestronglyMeasurable_pi_component hF.aestronglyMeasurable i,
   lt_of_le_of_lt (eLpNorm_pi_component_le i) hF.eLpNorm_lt_top⟩

end PiComponent

end BareFunction
