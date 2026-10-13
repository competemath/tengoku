/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.L2.BlockAverages

/-!
# Long averages and following tail averages

This file proves the `l2_bound_long_vs_tail` milestone from Layer 3 of the Exchangeability
roadmap.  It specializes the general two-window estimate for a contractable real-valued process
to the two canonical adjacent blocks

```text
{0, ..., n - 1}       and       {n, ..., 2 * n - 1}.
```

The resulting exact identity says that the squared `L²` distance between the prefix average
and the following tail average is `2 * (v - c) / n`, where `v` is the common coordinate
variance and `c` is the common off-diagonal covariance.  In particular this distance tends to
zero as the block length tends to infinity.  This is the long-average versus tail-average input
for the later weighted-sum convergence argument.

The proof uses the preceding Tau Ceti two-window identity
`Contractable.integral_sq_blockAverage_sub_of_disjoint`; the elementary limit is Mathlib's
`tendsto_one_div_add_atTop_nhds_zero_nat`.  The mathematical formulation follows Kallenberg,
*Probabilistic Symmetries and Invariance Principles* (Springer, 2005), Chapter 1, around
Theorem 1.1.  No material from `cameronfreer/exchangeability` is reused.

`prefixAverage` and `followingAverage` themselves involve no measure and are defined, with their
pointwise formulas, in `TauCeti.Probability.Process.BlockAverage`; this file adds the `L²` theory.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- A prefix average of `L²` coordinates is itself `L²`. -/
theorem memLp_prefixAverage (n : ℕ) (hX_L2 : ∀ i : Fin n, MemLp (X i) 2 μ) :
    MemLp (prefixAverage X n) 2 μ := by
  rw [prefixAverage_def]
  exact memLp_blockAverage (fun i : Fin n => (i : ℕ)) hX_L2

/-- A following tail average of `L²` coordinates is itself `L²`. -/
theorem memLp_followingAverage (n : ℕ) (hX_L2 : ∀ i : Fin n, MemLp (X (n + i)) 2 μ) :
    MemLp (followingAverage X n) 2 μ := by
  rw [followingAverage_def]
  exact memLp_blockAverage (fun i : Fin n => n + (i : ℕ)) hX_L2

end Probability

end TauCeti
