/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Tengoku.Seed.RingTheory.Valuation.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Newton-polygon dichotomy for a Weierstrass equation

Let `v` be a valuation on a field `K`, with values in an arbitrary linearly ordered commutative
group with zero, and let `W` be a Weierstrass curve over `K` **all of whose coefficients are
`v`-integral** (`v aᵢ ≤ 1`).  If a point `(x, y)` on `W` has a pole in the `x`-coordinate
(`1 < v x`), then it has one in the `y`-coordinate too, and

```
(v y) ^ 2 = (v x) ^ 3,
```

the multiplicative form of `2·ord y = 3·ord x`.  This is the statement that the Newton polygon of
the Weierstrass equation at a pole has the single slope `3/2` — the reason the point at infinity of
a Weierstrass curve is a *double* pole of `x` and a *triple* pole of `y`.

## Why the general value group

The argument never divides by `2` or by `3`; it only ever compares integer powers of `v x` and
`v y`.  So no discreteness assumption is needed, and in particular this applies to a valuation
whose value group is not yet known to be `ℤ`.  Two developments in this repository consume it at
different generality:

* `EllipticCurves.Reduction.PointValuation` — at `v = valuation K (maximalIdeal R)` for a discrete
  valuation ring `R` with `IsIntegral R W` (Silverman AEC VII.2 Prop 2.1, the kernel of reduction);
* `EllipticCurves.FunctionField.ValuationAtInfinity` — at an arbitrary valuation subring of the
  function field `F(W)` containing `F`, where discreteness is a *conclusion* rather than a
  hypothesis, and the value group is `O.ValueGroup`.

Stating it once, with the coefficient bounds as hypotheses, is what lets both use it.

## Main results

* `WeierstrassCurve.valuation_pow_two_eq_pow_three_of_valuation_le_one` — the dichotomy above;
* `WeierstrassCurve.valuation_le_one_of_valuation_le_one` — the complementary branch: if `v x ≤ 1`
  then `v y ≤ 1`.  Together the two say that a point of `W` is `v`-integral in `y` as soon as it is
  `v`-integral in `x`, which is the "no pole in `x`" half of the classification of the places of a
  function field.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1.
-/

namespace WeierstrassCurve

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- **Newton-polygon dichotomy for a Weierstrass equation.**  If every coefficient of `W` is
`v`-integral and a point `(x, y)` of `W` has `1 < v x`, then `1 < v y` and `(v y) ^ 2 = (v x) ^ 3`.

The proof takes the valuation of both sides of `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.  Since
`1 < v x` and every `v aᵢ ≤ 1`, the right side is dominated by `x³`, so `v (RHS) = (v x) ^ 3`.  On
the left, first `1 < v y` (else every term has valuation `≤ v x < (v x) ^ 3`), then a trichotomy on
`(v y) ^ 2` against `v (a₁xy + a₃y)` shows `(v y) ^ 2` is the strictly dominant term.

Every comparison is between integer powers of `v x` and `v y`; nothing is halved, so no
discreteness of `v` is used or needed. -/
theorem valuation_pow_two_eq_pow_three_of_valuation_le_one (v : Valuation K Γ₀)
    (W : WeierstrassCurve K) (ha1 : v W.a₁ ≤ 1) (ha2 : v W.a₂ ≤ 1) (ha3 : v W.a₃ ≤ 1)
    (ha4 : v W.a₄ ≤ 1) (ha6 : v W.a₆ ≤ 1) {x y : K} (heqn : W.toAffine.Equation x y)
    (hx : 1 < v x) : 1 < v y ∧ v y ^ 2 = v x ^ 3 := by
  set a : Γ₀ := v x with ha
  set b : Γ₀ := v y with hb
  -- The Weierstrass equation, valuation of both sides.
  rw [Affine.equation_iff] at heqn
  -- Powers of `a = v x` are increasing since `1 < a`.
  have ha0 : (0 : Γ₀) < a := zero_lt_one.trans hx
  have h1a3 : (1 : Γ₀) < a ^ 3 := one_lt_pow₀ hx (by norm_num)
  have ha2a3 : a ^ 2 < a ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
  have haa3 : a < a ^ 3 := by
    calc a = a ^ 1 := (pow_one a).symm
      _ < a ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
  -- `v (RHS) = a ^ 3`: the term `x ^ 3` strictly dominates.
  have hva2x2 : v (W.a₂ * x ^ 2) < a ^ 3 := by
    rw [map_mul, map_pow]
    calc v W.a₂ * a ^ 2 ≤ 1 * a ^ 2 := by gcongr
      _ = a ^ 2 := one_mul _
      _ < a ^ 3 := ha2a3
  have hva4x : v (W.a₄ * x) < a ^ 3 := by
    rw [map_mul]
    calc v W.a₄ * a ≤ 1 * a := by gcongr
      _ = a := one_mul _
      _ < a ^ 3 := haa3
  have hva6 : v W.a₆ < a ^ 3 := lt_of_le_of_lt ha6 h1a3
  have hvx3 : v (x ^ 3) = a ^ 3 := by rw [map_pow]
  have hRHS : v (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = a ^ 3 := by
    have hgroup : x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
        = x ^ 3 + (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by ring
    have htail : v (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) < a ^ 3 :=
      Valuation.map_add_lt _ (Valuation.map_add_lt _ hva2x2 hva4x) hva6
    rw [hgroup, Valuation.map_add_eq_of_lt_left _ (hvx3.symm ▸ htail), hvx3]
  -- Step 1: `1 < b`.  Otherwise every term of the LHS has valuation `≤ a < a ^ 3`.
  have hb1 : 1 < b := by
    by_contra hcon
    rw [not_lt] at hcon  -- hcon : b ≤ 1
    have hvy2 : v (y ^ 2) < a ^ 3 := by
      rw [map_pow]
      calc b ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ zero_le hcon 2
        _ = 1 := one_pow 2
        _ < a ^ 3 := h1a3
    have hva1xy : v (W.a₁ * x * y) < a ^ 3 := by
      rw [map_mul, map_mul]
      calc v W.a₁ * a * b ≤ 1 * a * 1 := by gcongr
        _ = a := by rw [one_mul, mul_one]
        _ < a ^ 3 := haa3
    have hva3y : v (W.a₃ * y) < a ^ 3 := by
      rw [map_mul]
      calc v W.a₃ * b ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
        _ < a ^ 3 := h1a3
    have hLHS : v (y ^ 2 + W.a₁ * x * y + W.a₃ * y) < a ^ 3 :=
      Valuation.map_add_lt _ (Valuation.map_add_lt _ hvy2 hva1xy) hva3y
    rw [heqn, hRHS] at hLHS
    exact lt_irrefl _ hLHS
  -- Step 2: `(v y)^2 = (v x)^3`.  Trichotomy on `b ^ 2` versus `v (a₁xy + a₃y)`.
  refine ⟨hb1, ?_⟩
  -- `v (a₁xy) ≤ a * b` and `v (a₃y) ≤ b`.
  have hva1xy_le : v (W.a₁ * x * y) ≤ a * b := by
    rw [map_mul, map_mul]
    calc v W.a₁ * a * b ≤ 1 * a * b := by gcongr
      _ = a * b := by rw [one_mul]
  have hva3y_le : v (W.a₃ * y) ≤ b := by
    rw [map_mul]
    calc v W.a₃ * b ≤ 1 * b := by gcongr
      _ = b := one_mul _
  -- Let `T = a₁xy + a₃y`; then `v T ≤ a * b` and `v (LHS) = v (y² + T)`.
  set T : K := W.a₁ * x * y + W.a₃ * y with hT
  have hbab : b ≤ a * b := by
    calc b = 1 * b := (one_mul _).symm
      _ ≤ a * b := mul_le_mul_left hx.le b
  have hvT : v T ≤ a * b :=
    le_trans (Valuation.map_add _ _ _) (max_le hva1xy_le (le_trans hva3y_le hbab))
  -- `v (LHS)` in terms of `b ^ 2` and `v T`.
  have hLHS_eq : v (y ^ 2 + T) = a ^ 3 := by
    have : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y ^ 2 + T := by rw [hT]; ring
    rw [← this, heqn, hRHS]
  -- Trichotomy on `b ^ 2` vs `v T`.
  rcases lt_trichotomy (v T) (b ^ 2) with hlt | heq | hgt
  · -- `v T < b ^ 2`: `y²` dominates, so `v (LHS) = b ^ 2 = a ^ 3`.
    have : v (y ^ 2 + T) = b ^ 2 := by
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hlt), map_pow]
    rw [hLHS_eq] at this
    exact this.symm
  · -- `v T = b ^ 2`: then `a ^ 3 = v (LHS) ≤ b ^ 2` and `b ^ 2 = v T ≤ a * b ⟹ b ≤ a`,
    -- giving `a ^ 3 ≤ b ^ 2 ≤ a ^ 2 < a ^ 3`, contradiction.
    exfalso
    have hb2ab : b ^ 2 ≤ a * b := by rw [← heq]; exact hvT
    have hb0 : (0 : Γ₀) < b := zero_lt_one.trans hb1
    have hba : b ≤ a := by
      rw [pow_two] at hb2ab
      exact (mul_le_mul_iff_left₀ hb0).mp hb2ab
    have hle : a ^ 3 ≤ b ^ 2 := by
      have hmax : v (y ^ 2 + T) ≤ b ^ 2 := by
        refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (le_of_eq heq))
        rw [map_pow]
      rw [hLHS_eq] at hmax; exact hmax
    have hb2a2 : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ zero_le hba 2
    exact absurd (lt_of_le_of_lt (le_trans hle hb2a2) ha2a3) (lt_irrefl _)
  · -- `b ^ 2 < v T`: then `v (LHS) = v T = a ^ 3 ≤ a * b`, so `a ^ 2 ≤ b`, hence
    -- `a ^ 4 ≤ b ^ 2 < a ^ 3`, contradicting `a ^ 3 < a ^ 4`.
    exfalso
    have hLHS_T : v (y ^ 2 + T) = v T := by
      rw [Valuation.map_add_eq_of_lt_right _ (by rw [map_pow]; exact hgt)]
    rw [hLHS_eq] at hLHS_T  -- hLHS_T : a ^ 3 = v T
    have ha3ab : a ^ 3 ≤ a * b := by rw [hLHS_T]; exact hvT
    have hb2a3 : b ^ 2 < a ^ 3 := by rw [hLHS_T]; exact hgt
    have ha2b : a ^ 2 ≤ b := by
      have h : a * a ^ 2 ≤ a * b := by rw [← pow_succ']; exact ha3ab
      exact (mul_le_mul_iff_right₀ ha0).mp h
    have ha4b2 : a ^ 4 ≤ b ^ 2 := by
      calc a ^ 4 = (a ^ 2) ^ 2 := by rw [← pow_mul]
        _ ≤ b ^ 2 := pow_le_pow_left₀ zero_le ha2b 2
    have ha4a3 : a ^ 4 < a ^ 3 := lt_of_le_of_lt ha4b2 hb2a3
    have ha3a4 : a ^ 3 < a ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    exact absurd ha4a3 (not_lt.mpr (le_of_lt ha3a4))

/-- **The complementary branch of the dichotomy.**  If every coefficient of `W` is `v`-integral and
a point `(x, y)` of `W` has `v x ≤ 1`, then `v y ≤ 1` as well: an affine point cannot have a pole in
`y` alone.

Classically this is the statement that `y` is integral over `R[x]`, obtained from the monic
quadratic `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)` that `y` satisfies; the valuation-theoretic
proof below avoids any integral-closure API.  If `1 < v y` then `v (y²) = (v y)²` strictly dominates
both `v (a₁xy) ≤ v y` and `v (a₃y) ≤ v y`, so the left side of the Weierstrass equation has
valuation `(v y)² > 1`, while every term on the right is `v`-integral.

As with the other branch, no discreteness of `v` is used. -/
theorem valuation_le_one_of_valuation_le_one (v : Valuation K Γ₀) (W : WeierstrassCurve K)
    (ha1 : v W.a₁ ≤ 1) (ha2 : v W.a₂ ≤ 1) (ha3 : v W.a₃ ≤ 1) (ha4 : v W.a₄ ≤ 1)
    (ha6 : v W.a₆ ≤ 1) {x y : K} (heqn : W.toAffine.Equation x y) (hx : v x ≤ 1) :
    v y ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  rw [Affine.equation_iff] at heqn
  have hy2 : (1 : Γ₀) < v y ^ 2 := one_lt_pow₀ hcon (by norm_num)
  -- every term on the right is integral
  have hx3 : v (x ^ 3) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le hx
  have hx2 : v (W.a₂ * x ^ 2) ≤ 1 := by
    rw [map_mul, map_pow]; exact mul_le_one' ha2 (pow_le_one₀ zero_le hx)
  have hx1 : v (W.a₄ * x) ≤ 1 := by rw [map_mul]; exact mul_le_one' ha4 hx
  have hRHS : v (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) ≤ 1 :=
    le_trans (Valuation.map_add _ _ _) (max_le
      (le_trans (Valuation.map_add _ _ _) (max_le
        (le_trans (Valuation.map_add _ _ _) (max_le hx3 hx2)) hx1)) ha6)
  -- on the left `y ^ 2` strictly dominates
  have hxy : v (W.a₁ * x * y) < v (y ^ 2) := by
    rw [map_mul, map_mul, map_pow, pow_two]
    calc v W.a₁ * v x * v y ≤ 1 * 1 * v y := by gcongr
      _ = 1 * v y := by rw [one_mul, one_mul]
      _ < v y * v y := (mul_lt_mul_iff_left₀ (zero_lt_one.trans hcon)).2 hcon
  have hy : v (W.a₃ * y) < v (y ^ 2) := by
    rw [map_mul, map_pow, pow_two]
    calc v W.a₃ * v y ≤ 1 * v y := by gcongr
      _ < v y * v y := (mul_lt_mul_iff_left₀ (zero_lt_one.trans hcon)).2 hcon
  have hLHS : v (y ^ 2 + W.a₁ * x * y + W.a₃ * y) = v y ^ 2 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by
      rwa [Valuation.map_add_eq_of_lt_left _ hxy]), Valuation.map_add_eq_of_lt_left _ hxy,
      map_pow]
  rw [← heqn, hLHS] at hRHS
  exact absurd hRHS (not_le.2 hy2)

end WeierstrassCurve
