/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Process.BlockAverage
public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.L2.Covariance

/-!
# Two-window L² bounds for block averages of a contractable sequence

This file continues the Layer 3 (L²) lane of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Layer 3: L² averaging library and the
standard-Borel de Finetti route"), building the "two-window L² bounds for block averages"
milestone (`l2_bound_two_windows_uniform`) on top of the uniform covariance structure of a
contractable L² sequence (`contractable_covariance_structure`).

For a real-valued process `X : ℕ → Ω → ℝ` and a finite selection `k : Fin n → ℕ`, the
*block average* `blockAverage X k = n⁻¹ • ∑ i, X (k i)` is the empirical mean of the block
`(X (k i))ᵢ`; it is defined, with its measure-free algebra, in
`TauCeti.Probability.Process.BlockAverage`.
When `X` is contractable with `L²` coordinates, its second-moment structure is
uniform: all coordinate variances agree and all off-diagonal covariances agree
(`contractable_covariance_structure`). Writing `v = Var[X 0]` and `c = cov[X 0, X 1]`, this
uniformity forces the block average to have the explicit variance

```text
Var[blockAverage X k] = (v - c) / n + c,
```

and any two blocks over *disjoint* index sets to have covariance exactly `c`. Consequently two
disjoint block averages of lengths `n` and `m` satisfy

```text
Var[blockAverage X k - blockAverage X k'] = (v - c) / n + (v - c) / m,
```

and, since contractability makes the two averages share the common mean `μ[X 0]`, this is the
squared `L²` distance `∫ (blockAverage X k - blockAverage X k')² dμ` itself. The squared
distance vanishes like `1 / n + 1 / m` (equivalently, the `L²` norm like `n^(-1/2)` for equal
windows), which is the quantitative averaging input the `L²` route runs on: it is what drives the
convergence of `blockAverage X k` toward the common conditional mean.

The elementary L² route to de Finetti's theorem formalised here is the one presented in
Kallenberg, *Probabilistic Symmetries and Invariance Principles* (Springer, 2005), Chapter 1
(around Theorem 1.1); the Lean identities below were derived independently.

The covariance/variance bilinearity (`ProbabilityTheory.covariance_sum_sum`,
`variance_sum`, `covariance_smul_left`, `variance_const_mul`) and the integral manipulations are
Mathlib's; the contractability input is the Layer 0/3 API in
`TauCeti.Probability.Exchangeability.Contractability` and
`TauCeti.Probability.Exchangeability.L2.Covariance`. No material from
`cameronfreer/exchangeability` is reused: the source carries the block-average bounds through a
different, sequence-specific `L²` development, whereas this file records the closed-form
second-moment identities directly.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- A block average of `L²` coordinates is itself `L²`. -/
theorem memLp_blockAverage {n : ℕ} (k : Fin n → ℕ) (hX_L2 : ∀ i, MemLp (X (k i)) 2 μ) :
    MemLp (blockAverage X k) 2 μ := by
  rw [blockAverage_eq_sum]
  exact (memLp_finsetSum' _ fun i _ => hX_L2 i).const_smul _

/-- **Conditional expectation commutes with block averages.** The conditional expectation of a
block average of integrable coordinates is the block average of their conditional expectations. -/
theorem condExp_blockAverage {m : MeasurableSpace Ω} {n : ℕ} (k : Fin n → ℕ)
    (hX : ∀ i, Integrable (X (k i)) μ) :
    μ[blockAverage X k | m] =ᵐ[μ] blockAverage (fun i => μ[X i | m]) k := by
  rw [blockAverage_eq_sum]
  refine (condExp_smul _ _ _).trans ?_
  filter_upwards [condExp_finsetSum (μ := μ) (m := m) (s := Finset.univ)
    (f := fun i : Fin n => X (k i)) fun i _ => hX i] with ω hω
  rw [Pi.smul_apply, hω, Finset.sum_apply, blockAverage_apply, smul_eq_mul]

end Probability

end TauCeti
