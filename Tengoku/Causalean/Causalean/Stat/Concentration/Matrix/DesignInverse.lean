/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Stat.Concentration.Matrix.InversePerturbation
public import Tengoku.Causalean.Causalean.Stat.Concentration.Matrix.InverseUnionBound

/-!
# Matrix-inverse concentration for the random design moment matrix

Assembles deterministic inverse perturbation and iid union bounds into concentration for random
design moment-matrix inverses.

This module assembles the two halves of the interior local-polynomial leverage rate
`(M⁻¹)₀₀ = O(1/(Nh))` for the **random** design:

* `Perturbation.designInv00_perturb` — the deterministic transport: if the empirical moment
  matrix `M` is entrywise within `η` of an invertible population matrix `S` whose inverse has
  row sums bounded by `c`, with `c·(p+1)·η ≤ 1/2`, then `M` is invertible and
  `|(M⁻¹)₀₀ − (S⁻¹)₀₀| ≤ 2 c² (p+1) η`.
* `UnionBound.iid_sum_union_bound` — the probabilistic half: each entry `M_{jk}(ω) = ∑ᵢ g_{jk}(ωᵢ)`
  is an iid sum, so a union bound over the `(p+1)²` entries makes the entrywise-`η` good event
  have probability `≥ 1 − ∑ Var/η²`.

The capstone `designMatrix_inv_concentration` combines them: the analytic failure event
(`M` singular, or `(M⁻¹)₀₀` far from `(S⁻¹)₀₀`) has probability at most the union-bound tail.
Here the population matrix `S = 𝔼[M]` is supplied with its invertibility (`IsUnit S.det`, e.g. from
`designMatrix_posDef`) and an inverse-row-sum bound `c`; turning those into the explicit `Θ(Nh)`
density constants is the remaining kernel-change-of-variables step.
-/

public section

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

end Causalean.Stat.Concentration
