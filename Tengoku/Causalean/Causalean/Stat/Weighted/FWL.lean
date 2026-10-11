/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Weighted FWL coefficient uniqueness

This file proves the coefficient-uniqueness direction of the
Frisch-Waugh-Lovell identity for the `Causalean.Stat.Weighted` substrate. Let
`c : WeightedSupport R` be a weighted support, `H : Submodule ℝ (R → ℝ)` a
nuisance subspace, and `X : Fin K → R → ℝ` a regressor vector. If a pair
`(β, α)` minimizes

    ω-WLS objective  c.ip (Y - ∑ k β k • X k - α) (Y - ∑ k β k • X k - α)

over all `(β : Fin K → ℝ, α ∈ H)`, then `β` equals the residualized
coefficient `θ̂ := Q_XX⁻¹ * ⟨X̃, Y⟩_ω`, where
`X̃ := c.tildeXVec H X`.

The theorem identifies the coefficient of any supplied joint minimizer. It
does not construct a minimizer or prove that `thetaHat` minimizes a residualized
least-squares objective.

## Main definitions

* `Q_XX` — the residualized Gram matrix `⟨X̃, X̃⟩_ω`.
* `rhsVec` — the residualized RHS `⟨X̃, Y⟩_ω`.
* `thetaHat` — the FWL coefficient `Q_XX⁻¹ * rhsVec`.
* `RankCondition` — nonsingularity of `Q_XX`.

## Main results

* `Q_XX_mulVec_thetaHat` — `thetaHat` solves the residualized normal equations.
* `fwl_identity` — long-regression joint minimizer `β` equals `thetaHat`.
-/

module
public import Tengoku.Causalean.Causalean.Stat.Weighted.WLS
public import Tengoku

/-! # Weighted FWL coefficient uniqueness

This file states and proves the coefficient-uniqueness direction of the finite
weighted-support Frisch-Waugh-Lovell identity. It constructs the residualized Gram matrix
`Q_XX`, residualized score vector `rhsVec`, residualized coefficient
`thetaHat`, and rank condition `RankCondition`. The lemma
`Q_XX_mulVec_thetaHat` proves that `thetaHat` solves the residualized normal
equations, and the theorem `fwl_identity` proves that any long weighted
least-squares minimizer has coefficient `thetaHat` after residualizing against
the nuisance space. -/

@[expose] public section

open scoped BigOperators
open Matrix

namespace Causalean
namespace Stat.Weighted
namespace WeightedSupport

variable {R : Type*}
variable [Fintype R] [DecidableEq R]
variable {K : ℕ}

/-! ### Residualized regression objects -/

/-! ### Frisch–Waugh–Lovell identity

The headline theorem of the substrate.  Joint minimization in `(β, α)` over
`(Fin K → ℝ) × H` of the long-regression WLS objective forces
`β = thetaHat`. -/

/-- For a weighted inner product, the inner product of a finite sum of functions with another
function equals the corresponding finite sum of inner products.
@isnad1 id=eq.0h6v.s6.b497a73d2840 from=translated src=- shape=edf02692 vocab=2e0fc6d0
-/
lemma ip_sum_left_finset (c : WeightedSupport R) {ι : Type*}
    (s : Finset ι) (f : ι → R → ℝ) (B : R → ℝ) :
    c.ip (∑ i ∈ s, f i) B = ∑ i ∈ s, c.ip (f i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert a s' hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, c.ip_add_left, ih]

private lemma ip_sum_left (c : WeightedSupport R)
    (f : Fin K → R → ℝ) (B : R → ℝ) :
    c.ip (∑ k, f k) B = ∑ k, c.ip (f k) B :=
  c.ip_sum_left_finset Finset.univ f B

/-- The weighted inner product of a function with a finite sum of functions
    equals the sum of its weighted inner products with the summands.
@isnad1 id=eq.0h5v.s6.d425cae83a61 from=translated src=- shape=dbd75a4a vocab=b16ab3d4
-/
lemma ip_sum_right (c : WeightedSupport R)
    (A : R → ℝ) (f : Fin K → R → ℝ) :
    c.ip A (∑ k, f k) = ∑ k, c.ip A (f k) := by
  rw [c.ip_symm, c.ip_sum_left]
  refine Finset.sum_congr rfl ?_
  intro k _; exact c.ip_symm _ _

end WeightedSupport
end Stat.Weighted
end Causalean
