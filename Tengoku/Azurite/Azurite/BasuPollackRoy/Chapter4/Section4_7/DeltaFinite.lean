/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_7.SingularLocus
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_7.DiagonalCount
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_7.Lemma_4_102

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.7, Proposition 4.106: the singular-parameter set `Δ` is finite

The projection `Δ ⊆ ℙ₁(C)` of the singular locus (the parameters `(λ : µ)` for which the system
`S₍λ:µ₎` has a singular projective zero) is algebraic (`delta_isAlgebraic`, via Theorem 4.103). It is
moreover a *proper* algebraic subset of `ℙ₁(C)`: the parameter `(0 : 1)` is not in `Δ`, since
`S₍₀:₁₎` is the diagonal system, whose common zeros are **all** non-singular
(`diagSystem_common_zero_isNonsingular`, Lemma B). By Lemma 4.102, a proper algebraic subset of
`ℙ₁(C)` is finite. Hence `Δ` is finite.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- At the parameter `(0 : 1)` the pencil is `c · Dᵢ` (`c ≠ 0`), the diagonal system up to a unit. By
Lemma B all its common zeros are non-singular, so it has **no** singular projective zero: a common
zero with rank-deficient Jacobian is impossible.-/
theorem not_singular_at_diag (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (x : complexProjectiveSpace R k) (c : Ri R) (hc : c ≠ 0)
    (hcz : ∀ i, aeval x.rep (homotopyPoly P d 0 c i) = 0)
    (hrank : (projJacobian (homotopyPoly P d 0 c) x).rank < k) : False := by
  have hhp : ∀ i : Fin k, homotopyPoly P d 0 c i
      = (C c * diagFactor (d i) i : MvPolynomial (Fin (k + 1)) (Ri R)) := by
    intro i; rw [homotopyPoly, map_zero, zero_mul, zero_add]
  -- `x` is a common zero of the diagonal system
  have hcommon : ∀ i, aeval x.rep (diagSystem (R := R) d i) = 0 := by
    intro i
    have h := hcz i
    rw [hhp i, map_mul] at h
    rw [diagSystem]
    refine (mul_eq_zero.mp h).resolve_left ?_
    rw [aeval_C]; simpa using hc
  -- by Lemma B the diagonal Jacobian has full rank `k`
  have hrankeq : (projJacobian (diagSystem d) x).rank = k :=
    (diagSystem_common_zero_isNonsingular d hd x hcommon).2
  -- the pencil Jacobian at `(0:1)` is `c · (diagonal Jacobian)`, hence has the same rank `k`
  have hjeq : projJacobian (homotopyPoly P d 0 c) x
      = Matrix.diagonal (fun _ : Fin k => c) * projJacobian (diagSystem d) x := by
    ext i j
    rw [Matrix.diagonal_mul, projJacobian, Matrix.of_apply, projJacobian, Matrix.of_apply,
      hhp i, diagSystem, pderiv_C_mul, map_mul, aeval_C]
    simp
  have hmul : (Matrix.diagonal (fun _ : Fin k => c) * projJacobian (diagSystem d) x).rank
      = (projJacobian (diagSystem d) x).rank := by
    apply Matrix.rank_mul_eq_right_of_isUnit_det
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => hc)
  rw [hjeq, hmul, hrankeq] at hrank
  exact lt_irrefl k hrank

end Azurite.BPR.Chapter4
