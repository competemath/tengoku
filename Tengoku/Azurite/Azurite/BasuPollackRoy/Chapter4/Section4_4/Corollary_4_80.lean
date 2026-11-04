/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_78
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR Corollary 4.80: Homogeneous Hilbert's Nullstellensatz

Let `𝒫 = {P₁, …, P_s}` be homogeneous with `deg(Pᵢ) = dᵢ`, and `P` homogeneous of degree `p`
vanishing on the common zeros of `𝒫` in `C^k` (`K` of characteristic zero, `C` algebraically
closed, `0 < p`). Then there are `n` and homogeneous `Hᵢ` of degree `cᵢ = np - dᵢ` with
`P^n = ∑ᵢ Hᵢ Pᵢ` and `np = cᵢ + dᵢ`.

The Hᵢ are the degree-`np` homogeneous components of the coefficients in the (ordinary)
Nullstellensatz combination `P^n = ∑ Bᵢ Pᵢ` (Theorem 4.78), `n` chosen large enough that
`np ≥ dᵢ`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {K : Type*} [Field K]

/-- Homogeneous component of a product with a homogeneous factor: if `Q` is homogeneous of degree
`e` and `e ≤ m`, then the degree-`m` component of `B * Q` is `(degree-(m-e) component of B) * Q`.
@isnad1 id=eq.2h6v.s9.938af7f730e7 from=translated src=- shape=ae987094 vocab=52170399
-/
theorem homogeneousComponent_mul_homogeneous {k : ℕ} {R : Type*} [CommRing R]
    {Q : MvPolynomial (Fin k) R} {e : ℕ} (hQ : Q.IsHomogeneous e) (m : ℕ) (hm : e ≤ m)
    (B : MvPolynomial (Fin k) R) :
    homogeneousComponent m (B * Q) = homogeneousComponent (m - e) B * Q := by
  conv_lhs => rw [← sum_homogeneousComponent B, Finset.sum_mul, map_sum]
  rw [Finset.sum_eq_single (m - e)]
  · -- the surviving term `j = m - e`
    have hh : (homogeneousComponent (m - e) B * Q).IsHomogeneous m := by
      have := (homogeneousComponent_isHomogeneous (m - e) B).mul hQ
      rwa [Nat.sub_add_cancel hm] at this
    rw [homogeneousComponent_of_mem hh, ite_eq_left rfl]
  · -- terms `j ≠ m - e` vanish
    intro j _ hjne
    have hh : (homogeneousComponent j B * Q).IsHomogeneous (j + e) :=
      (homogeneousComponent_isHomogeneous j B).mul hQ
    rw [homogeneousComponent_of_mem hh, ite_eq_right (by omega)]
  · -- `m - e ∉ range` means `homogeneousComponent (m - e) B = 0`
    intro hnot
    rw [Finset.mem_range, not_lt] at hnot
    rw [homogeneousComponent_eq_zero (m - e) B (by omega), zero_mul, map_zero]

end Azurite.BPR.Chapter4
