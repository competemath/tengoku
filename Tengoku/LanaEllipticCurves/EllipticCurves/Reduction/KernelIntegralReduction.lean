/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.TwoTorsionReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `redPt` additivity: the kernel × integral case (issue #384, closing #382)

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field `k`, and let
`W : WeierstrassCurve K` have good reduction.  This file proves the last genuinely-analytic case of
the homomorphism property `redPt (P + Q) = redPt P + redPt Q` of the point-reduction map: the
**kernel acts trivially** case.  For a pole point `P = (x₁, y₁)` in the kernel `E₁(K)` (`1 < v x₁`)
and an integral point `Q = (x₂, y₂)` (`v x₂ ≤ 1`),

```
redPt R W (P + Q) = redPt R W Q .
```

This is the well-definedness of the quotient map `E(K)/E₁ → Ẽ(k)`; it feeds the #383 assembly.

## The mechanism: a single Weierstrass substitution suffices

Since `1 < v x₁` while `v x₂ ≤ 1`, the two `x`-coordinates always have distinct valuations, so
`x₁ ≠ x₂` and `P + Q` is computed by the secant formula `add_of_X_ne`.  Writing `d = x₁ - x₂` (so
`v d = v x₁`), the Newton-polygon dichotomy gives `1 < v y₁` and `(v y₁)² = (v x₁)³`, whence
`v x₁ < (v x₁)²`, `v y₁ < (v x₁)²`, `v x₁ · v y₁ < (v x₁)³` and `(v x₁)² < (v x₁)³`.

The secant slope `ℓ = (y₁ - y₂)/d` satisfies `ℓ · d = y₁ - y₂` (no division).  Clearing denominators
and substituting the two Weierstrass equations *once* yields two **exact** polynomial identities

* `(addX - x₂) · d² = P₁`, where every monomial of `P₁` has `x₁`/`y₁`-weight `2i + 3j ≤ 3`;
* `(negAddY - negY x₂ y₂) · d³ = P₂`, with weight `2i + 3j ≤ 5`.

Grouping each `Pₖ` by the power of `x₁`, `y₁` makes every coefficient a polynomial purely in the
integral quantities `x₂, y₂, aᵢ` (valuation `≤ 1`), so `v P₁ ≤ v y₁ < (v x₁)² = v d²` and
`v P₂ ≤ v x₁ · v y₁ < (v x₁)³ = v d³`.  Hence `v (addX - x₂) < 1` and
`v (negAddY - negY x₂ y₂) < 1`, i.e. the reduced coordinates are exactly `x̄₂` and `ȳ₂` (the `+ȳ₂`,
not `-ȳ₂`, distinguishing `Q̄` from `-Q̄`).

## Main results

* `WeierstrassCurve.redPt_add_of_mem_E₁_left` — `redPt (P + Q) = redPt Q` for `P` a pole
  (`1 < v x₁`) and `Q` integral.
* `WeierstrassCurve.redPt_add_of_mem_E₁_right` — the symmetric `redPt (Q + P) = redPt Q`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1, VII.2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum WithZero Multiplicative

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### A point-equality helper and a residue-agnostic reduction lemma -/

/-- Two affine points with equal coordinates are equal (the nonsingularity proof is irrelevant). -/
private theorem point_some_congr {F : Type*} [Field F] {W' : WeierstrassCurve F}
    {x₁ x₂ y₁ y₂ : F} (h₁ : W'.toAffine.Nonsingular x₁ y₁) (h₂ : W'.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W'.toAffine.Point)
      = WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

/-- If an integral point `(X, Y)` is congruent modulo `𝔪` to lifts `x₀, y₀ : R` — i.e.
`v (X - x₀) < 1` and `v (Y - y₀) < 1` — then `redPt` sends it to the residues of `x₀, y₀`.  A
lift-agnostic strengthening of `redPt_some_eq` (which needs `X, Y` to be *exact* lifts). -/
private theorem redPt_some_of_sub_lt_one (W : WeierstrassCurve K) [HasGoodReduction R W]
    {X Y : K} {h : W.toAffine.Nonsingular X Y} {x₀ y₀ : R}
    (hX : valuation K (maximalIdeal R) (X - algebraMap R K x₀) < 1)
    (hY : valuation K (maximalIdeal R) (Y - algebraMap R K y₀) < 1)
    (hns : (reduction R W).toAffine.Nonsingular
      (IsLocalRing.residue R x₀) (IsLocalRing.residue R y₀)) :
    redPt R W (.some X Y h) = .some (IsLocalRing.residue R x₀) (IsLocalRing.residue R y₀) hns := by
  set v : Valuation K ℤᵐ⁰ := valuation K (maximalIdeal R) with hvdef
  have hXeq : X = (X - algebraMap R K x₀) + algebraMap R K x₀ := by ring
  have hxle : v X ≤ 1 := by
    rw [hXeq]; exact v.map_add_le (le_of_lt hX) (valuation_le_one (maximalIdeal R) x₀)
  have hyle : v Y ≤ 1 := valuation_y_le_one_of_le_one R W h.1 hxle
  obtain ⟨x₀', hx₀'⟩ := exists_lift_of_le_one hxle
  obtain ⟨y₀', hy₀'⟩ := exists_lift_of_le_one hyle
  have hxr : IsLocalRing.residue R x₀' = IsLocalRing.residue R x₀ := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hval : valuation K (maximalIdeal R) (algebraMap R K (x₀' - x₀)) < 1 := by
      rw [map_sub, hx₀']; exact hX
    exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) (x₀' - x₀)).mp hval
  have hyr : IsLocalRing.residue R y₀' = IsLocalRing.residue R y₀ := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hval : valuation K (maximalIdeal R) (algebraMap R K (y₀' - y₀)) < 1 := by
      rw [map_sub, hy₀']; exact hY
    exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) (y₀' - y₀)).mp hval
  rw [redPt_some_eq R W hx₀' hy₀' (by rw [hxr, hyr]; exact hns)]
  exact point_some_congr _ _ hxr hyr

/-! ### The kernel × integral secant lemma -/

open Classical in
/-- **`redPt` additivity, kernel × integral case.**  For a pole point `P = (x₁, y₁)` in `E₁(K)`
(`1 < v x₁`) and an integral point `Q = (x₂, y₂)` (`v x₂ ≤ 1`) with integral lifts `x₀₂, y₀₂` of
`x₂, y₂`, adding `P` fixes the reduction: `redPt (P + Q) = redPt Q`. -/
theorem redPt_add_of_mem_E₁_left (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ y₁ x₂ y₂ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    {x₀₂ y₀₂ : R} (hx₂ : algebraMap R K x₀₂ = x₂) (hy₂ : algebraMap R K y₀₂ = y₂)
    (hvx₂ : valuation K (maximalIdeal R) x₂ ≤ 1)
    (hpole : 1 < valuation K (maximalIdeal R) x₁) :
    redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = redPt R W (.some x₂ y₂ h₂) := by
  haveI : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  have hcurve : (integralModel R W).toAffine.map (algebraMap R K) = W.toAffine :=
    baseChange_integralModel_eq R W
  set im : WeierstrassCurve R := integralModel R W with him
  set v : Valuation K ℤᵐ⁰ := valuation K (maximalIdeal R) with hvdef
  -- `x₁ ≠ x₂` because their valuations differ.
  have hx12 : x₁ ≠ x₂ := fun h => absurd (h ▸ hpole) (not_lt.mpr hvx₂)
  have ha1 : (1 : ℤᵐ⁰) < v x₁ := hpole
  -- Newton-polygon dichotomy for the pole `P`: `1 < v y₁` and `(v y₁)² = (v x₁)³`.
  obtain ⟨hb1, hrel⟩ := valuation_pow_two_eq_pow_three_of_one_lt R W h₁.1 ha1
  -- Arithmetic of `v x₁, v y₁` in `ℤᵐ⁰`.
  have h_a_a2 : v x₁ < v x₁ ^ 2 := by
    calc v x₁ = v x₁ ^ 1 := (pow_one _).symm
      _ < v x₁ ^ 2 := pow_lt_pow_right₀ ha1 one_lt_two
  have h_a2_a3 : v x₁ ^ 2 < v x₁ ^ 3 := pow_lt_pow_right₀ ha1 (by norm_num)
  have h_a_a3 : v x₁ < v x₁ ^ 3 := lt_trans h_a_a2 h_a2_a3
  have h_1_a2 : (1 : ℤᵐ⁰) < v x₁ ^ 2 := one_lt_pow₀ ha1 two_ne_zero
  have h_1_a3 : (1 : ℤᵐ⁰) < v x₁ ^ 3 := one_lt_pow₀ ha1 three_ne_zero
  have h_b_a2 : v y₁ < v x₁ ^ 2 := by
    refine lt_of_pow_lt_pow_left₀ 2 zero_le ?_
    rw [hrel, ← pow_mul]
    exact pow_lt_pow_right₀ ha1 (by norm_num)
  have h_b_a3 : v y₁ < v x₁ ^ 3 := lt_trans h_b_a2 h_a2_a3
  have h_ab_a3 : v x₁ * v y₁ < v x₁ ^ 3 := by
    refine lt_of_pow_lt_pow_left₀ 2 zero_le ?_
    rw [mul_pow, hrel, ← pow_add, ← pow_mul]
    exact pow_lt_pow_right₀ ha1 (by norm_num)
  -- valuations of `d`, `d²`, `d³` with `d = x₁ - x₂`.
  have hvD : v (x₁ - x₂) = v x₁ := by
    have hneg : v (-x₂) < v x₁ := by
      rw [Valuation.map_neg]; exact lt_of_le_of_lt hvx₂ ha1
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ hneg]
  have hvD2 : v ((x₁ - x₂) ^ 2) = v x₁ ^ 2 := by rw [map_pow, hvD]
  have hvD3 : v ((x₁ - x₂) ^ 3) = v x₁ ^ 3 := by rw [map_pow, hvD]
  -- The secant slope and the no-division relation `ℓ · d = y₁ - y₂`.
  set ℓ : K := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  have hlD : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓdef, Affine.slope_of_X_ne hx12]
    exact div_mul_cancel₀ (y₁ - y₂) (sub_ne_zero.mpr hx12)
  -- The two Weierstrass equations, as `linear_combination` inputs.
  have hG1 := (W.toAffine.equation_iff' x₁ y₁).mp h₁.1
  have hG2 := (W.toAffine.equation_iff' x₂ y₂).mp h₂.1
  -- General additivity brick for valuations.
  have vlt : ∀ {g : ℤᵐ⁰} {p q : K}, v p < g → v q < g → v (p + q) < g := by
    intro g p q hp hq
    exact lt_of_le_of_lt (v.map_add_le (le_max_left _ _) (le_max_right _ _)) (max_lt hp hq)
  -- Grouped-coefficient valuation bounds (each coefficient is integral, `v ≤ 1`).
  have hA1 : v (2 * W.a₆ - y₂ * W.a₃ + x₂ * W.a₄ - x₂ * x₂ * x₂) ≤ 1 := by
    have hR : algebraMap R K (2 * im.a₆ - y₀₂ * im.a₃ + x₀₂ * im.a₄ - x₀₂ * x₀₂ * x₀₂)
        = 2 * W.a₆ - y₂ * W.a₃ + x₂ * W.a₄ - x₂ * x₂ * x₂ := by
      simp only [him, map_ofNat, map_add, map_sub, map_mul, integralModel_a₃_eq,
        integralModel_a₄_eq, integralModel_a₆_eq, hx₂, hy₂]
    rw [← hR]; exact valuation_le_one (maximalIdeal R) _
  have hB1 : v (W.a₄ - y₂ * W.a₁ + 2 * x₂ * W.a₂ + 3 * x₂ * x₂) ≤ 1 := by
    have hR : algebraMap R K (im.a₄ - y₀₂ * im.a₁ + 2 * x₀₂ * im.a₂ + 3 * x₀₂ * x₀₂)
        = W.a₄ - y₂ * W.a₁ + 2 * x₂ * W.a₂ + 3 * x₂ * x₂ := by
      simp only [him, map_ofNat, map_add, map_sub, map_mul, integralModel_a₁_eq,
        integralModel_a₂_eq, integralModel_a₄_eq, hx₂, hy₂]
    rw [← hR]; exact valuation_le_one (maximalIdeal R) _
  have hC1 : v (-W.a₃ - 2 * y₂ - x₂ * W.a₁) ≤ 1 := by
    have hR : algebraMap R K (-im.a₃ - 2 * y₀₂ - x₀₂ * im.a₁)
        = -W.a₃ - 2 * y₂ - x₂ * W.a₁ := by
      simp only [him, map_ofNat, map_sub, map_neg, map_mul, integralModel_a₁_eq,
        integralModel_a₃_eq, hx₂, hy₂]
    rw [← hR]; exact valuation_le_one (maximalIdeal R) _
  -- Certificate 1: `(addX - x₂) · d² = A1 + x₁·B1 + y₁·C1`.
  have key1 : (W.toAffine.addX x₁ x₂ ℓ - x₂) * (x₁ - x₂) ^ 2
      = (2 * W.a₆ - y₂ * W.a₃ + x₂ * W.a₄ - x₂ * x₂ * x₂)
        + x₁ * (W.a₄ - y₂ * W.a₁ + 2 * x₂ * W.a₂ + 3 * x₂ * x₂)
        + y₁ * (-W.a₃ - 2 * y₂ - x₂ * W.a₁) := by
    simp only [Affine.addX]
    linear_combination
      (-y₂ - x₂ * W.a₁ - x₂ * ℓ + y₁ + x₁ * W.a₁ + x₁ * ℓ) * hlD + hG1 + hG2
  -- Conclude `v (addX - x₂) < 1`.
  have haddX : v (W.toAffine.addX x₁ x₂ ℓ - x₂) < 1 := by
    have hle : v ((W.toAffine.addX x₁ x₂ ℓ - x₂) * (x₁ - x₂) ^ 2) < v x₁ ^ 2 := by
      rw [key1]
      refine vlt (vlt (lt_of_le_of_lt hA1 h_1_a2) ?_) ?_
      · rw [Valuation.map_mul]
        calc v x₁ * v (W.a₄ - y₂ * W.a₁ + 2 * x₂ * W.a₂ + 3 * x₂ * x₂)
            ≤ v x₁ * 1 := by gcongr
          _ = v x₁ := mul_one _
          _ < v x₁ ^ 2 := h_a_a2
      · rw [Valuation.map_mul]
        calc v y₁ * v (-W.a₃ - 2 * y₂ - x₂ * W.a₁)
            ≤ v y₁ * 1 := by gcongr
          _ = v y₁ := mul_one _
          _ < v x₁ ^ 2 := h_b_a2
    rw [Valuation.map_mul, hvD2] at hle
    exact lt_of_mul_lt_mul_right (by rw [one_mul]; exact hle) zero_le
  -- Certificate 2 coefficient bounds.
  have hA2 : v (-4 * y₂ * W.a₆ - y₂ * W.a₃ * W.a₃ + x₂ * W.a₃ * W.a₄ - x₂ * W.a₁ * W.a₆
      - x₂ * y₂ * W.a₄ - x₂ * y₂ * W.a₁ * W.a₃ + x₂ * x₂ * W.a₂ * W.a₃ - x₂ * x₂ * x₂ * y₂
      - x₂ * x₂ * x₂ * x₂ * W.a₁) ≤ 1 := by
    have hR : algebraMap R K (-4 * y₀₂ * im.a₆ - y₀₂ * im.a₃ * im.a₃ + x₀₂ * im.a₃ * im.a₄
        - x₀₂ * im.a₁ * im.a₆ - x₀₂ * y₀₂ * im.a₄ - x₀₂ * y₀₂ * im.a₁ * im.a₃
        + x₀₂ * x₀₂ * im.a₂ * im.a₃ - x₀₂ * x₀₂ * x₀₂ * y₀₂ - x₀₂ * x₀₂ * x₀₂ * x₀₂ * im.a₁)
        = -4 * y₂ * W.a₆ - y₂ * W.a₃ * W.a₃ + x₂ * W.a₃ * W.a₄ - x₂ * W.a₁ * W.a₆
          - x₂ * y₂ * W.a₄ - x₂ * y₂ * W.a₁ * W.a₃ + x₂ * x₂ * W.a₂ * W.a₃ - x₂ * x₂ * x₂ * y₂
          - x₂ * x₂ * x₂ * x₂ * W.a₁ := by
      simp only [him, map_ofNat, map_add, map_sub, map_neg, map_mul, integralModel_a₁_eq,
        integralModel_a₂_eq, integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq,
        hx₂, hy₂]
    rw [← hR]; exact valuation_le_one (maximalIdeal R) _
  have hB2 : v (-W.a₃ * W.a₄ + W.a₁ * W.a₆ - 3 * y₂ * W.a₄ - y₂ * W.a₁ * W.a₃
      - 2 * x₂ * y₂ * W.a₂ - x₂ * y₂ * W.a₁ * W.a₁ + 3 * x₂ * x₂ * W.a₃ + x₂ * x₂ * W.a₁ * W.a₂
      + 3 * x₂ * x₂ * y₂ + 4 * x₂ * x₂ * x₂ * W.a₁) ≤ 1 := by
    have hR : algebraMap R K (-im.a₃ * im.a₄ + im.a₁ * im.a₆ - 3 * y₀₂ * im.a₄ - y₀₂ * im.a₁ * im.a₃
        - 2 * x₀₂ * y₀₂ * im.a₂ - x₀₂ * y₀₂ * im.a₁ * im.a₁ + 3 * x₀₂ * x₀₂ * im.a₃
        + x₀₂ * x₀₂ * im.a₁ * im.a₂ + 3 * x₀₂ * x₀₂ * y₀₂ + 4 * x₀₂ * x₀₂ * x₀₂ * im.a₁)
        = -W.a₃ * W.a₄ + W.a₁ * W.a₆ - 3 * y₂ * W.a₄ - y₂ * W.a₁ * W.a₃
          - 2 * x₂ * y₂ * W.a₂ - x₂ * y₂ * W.a₁ * W.a₁ + 3 * x₂ * x₂ * W.a₃ + x₂ * x₂ * W.a₁ * W.a₂
          + 3 * x₂ * x₂ * y₂ + 4 * x₂ * x₂ * x₂ * W.a₁ := by
      simp only [him, map_ofNat, map_add, map_sub, map_neg, map_mul, integralModel_a₁_eq,
        integralModel_a₂_eq, integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq,
        hx₂, hy₂]
    rw [← hR]; exact valuation_le_one (maximalIdeal R) _
  have hC2 : v (4 * W.a₆ + W.a₃ * W.a₃ + 3 * x₂ * W.a₄ + x₂ * W.a₁ * W.a₃ - x₂ * y₂ * W.a₁
      + 2 * x₂ * x₂ * W.a₂ + x₂ * x₂ * x₂) ≤ 1 := by
    have hR : algebraMap R K (4 * im.a₆ + im.a₃ * im.a₃ + 3 * x₀₂ * im.a₄ + x₀₂ * im.a₁ * im.a₃
        - x₀₂ * y₀₂ * im.a₁ + 2 * x₀₂ * x₀₂ * im.a₂ + x₀₂ * x₀₂ * x₀₂)
        = 4 * W.a₆ + W.a₃ * W.a₃ + 3 * x₂ * W.a₄ + x₂ * W.a₁ * W.a₃ - x₂ * y₂ * W.a₁
          + 2 * x₂ * x₂ * W.a₂ + x₂ * x₂ * x₂ := by
      simp only [him, map_ofNat, map_add, map_sub, map_mul, integralModel_a₁_eq,
        integralModel_a₂_eq, integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq,
        hx₂, hy₂]
    rw [← hR]; exact valuation_le_one (maximalIdeal R) _
  have hF2 : v (W.a₄ + W.a₁ * W.a₃ + y₂ * W.a₁ + 2 * x₂ * W.a₂ + x₂ * W.a₁ * W.a₁
      + 3 * x₂ * x₂) ≤ 1 := by
    have hR : algebraMap R K (im.a₄ + im.a₁ * im.a₃ + y₀₂ * im.a₁ + 2 * x₀₂ * im.a₂
        + x₀₂ * im.a₁ * im.a₁ + 3 * x₀₂ * x₀₂)
        = W.a₄ + W.a₁ * W.a₃ + y₂ * W.a₁ + 2 * x₂ * W.a₂ + x₂ * W.a₁ * W.a₁ + 3 * x₂ * x₂ := by
      simp only [him, map_ofNat, map_add, map_mul, integralModel_a₁_eq,
        integralModel_a₂_eq, integralModel_a₃_eq, integralModel_a₄_eq, hx₂, hy₂]
    rw [← hR]; exact valuation_le_one (maximalIdeal R) _
  have hE2 : v (-W.a₂ * W.a₃ - 2 * y₂ * W.a₂ - 3 * x₂ * W.a₃ - x₂ * W.a₁ * W.a₂ - 6 * x₂ * y₂
      - 3 * x₂ * x₂ * W.a₁) ≤ 1 := by
    have hR : algebraMap R K (-im.a₂ * im.a₃ - 2 * y₀₂ * im.a₂ - 3 * x₀₂ * im.a₃
        - x₀₂ * im.a₁ * im.a₂ - 6 * x₀₂ * y₀₂ - 3 * x₀₂ * x₀₂ * im.a₁)
        = -W.a₂ * W.a₃ - 2 * y₂ * W.a₂ - 3 * x₂ * W.a₃ - x₂ * W.a₁ * W.a₂ - 6 * x₂ * y₂
          - 3 * x₂ * x₂ * W.a₁ := by
      simp only [him, map_ofNat, map_sub, map_neg, map_mul, integralModel_a₁_eq,
        integralModel_a₂_eq, integralModel_a₃_eq, hx₂, hy₂]
    rw [← hR]; exact valuation_le_one (maximalIdeal R) _
  -- Certificate 2: `(negAddY - negY x₂ y₂) · d³ = A2 + x₁·B2 + y₁·C2 + x₁·y₁·F2 + x₁²·E2`.
  have key2 : (W.toAffine.negAddY x₁ x₂ y₁ ℓ - W.toAffine.negY x₂ y₂) * (x₁ - x₂) ^ 3
      = (-4 * y₂ * W.a₆ - y₂ * W.a₃ * W.a₃ + x₂ * W.a₃ * W.a₄ - x₂ * W.a₁ * W.a₆
          - x₂ * y₂ * W.a₄ - x₂ * y₂ * W.a₁ * W.a₃ + x₂ * x₂ * W.a₂ * W.a₃ - x₂ * x₂ * x₂ * y₂
          - x₂ * x₂ * x₂ * x₂ * W.a₁)
        + x₁ * (-W.a₃ * W.a₄ + W.a₁ * W.a₆ - 3 * y₂ * W.a₄ - y₂ * W.a₁ * W.a₃
          - 2 * x₂ * y₂ * W.a₂ - x₂ * y₂ * W.a₁ * W.a₁ + 3 * x₂ * x₂ * W.a₃ + x₂ * x₂ * W.a₁ * W.a₂
          + 3 * x₂ * x₂ * y₂ + 4 * x₂ * x₂ * x₂ * W.a₁)
        + y₁ * (4 * W.a₆ + W.a₃ * W.a₃ + 3 * x₂ * W.a₄ + x₂ * W.a₁ * W.a₃ - x₂ * y₂ * W.a₁
          + 2 * x₂ * x₂ * W.a₂ + x₂ * x₂ * x₂)
        + x₁ * y₁ * (W.a₄ + W.a₁ * W.a₃ + y₂ * W.a₁ + 2 * x₂ * W.a₂ + x₂ * W.a₁ * W.a₁
          + 3 * x₂ * x₂)
        + x₁ ^ 2 * (-W.a₂ * W.a₃ - 2 * y₂ * W.a₂ - 3 * x₂ * W.a₃ - x₂ * W.a₁ * W.a₂ - 6 * x₂ * y₂
          - 3 * x₂ * x₂ * W.a₁) := by
    simp only [Affine.negAddY, Affine.addX, Affine.negY]
    linear_combination
      (y₂ * y₂ + x₂ * y₂ * W.a₁ + x₂ * y₂ * ℓ - x₂ * x₂ * W.a₂ + x₂ * x₂ * ℓ * W.a₁
        + x₂ * x₂ * ℓ * ℓ - x₂ * x₂ * x₂ - 2 * y₁ * y₂ - y₁ * x₂ * W.a₁ - y₁ * x₂ * ℓ + y₁ * y₁
        - x₁ * y₂ * W.a₁ - x₁ * y₂ * ℓ + 2 * x₁ * x₂ * W.a₂ - 2 * x₁ * x₂ * ℓ * W.a₁
        - 2 * x₁ * x₂ * ℓ * ℓ + x₁ * y₁ * W.a₁ + x₁ * y₁ * ℓ - x₁ * x₁ * W.a₂ + x₁ * x₁ * ℓ * W.a₁
        + x₁ * x₁ * ℓ * ℓ + 3 * x₁ * x₁ * x₂ - 2 * x₁ * x₁ * x₁) * hlD
      + (-W.a₃ - 3 * y₂ - x₂ * W.a₁ + y₁) * hG1
      + (W.a₃ - y₂ + 3 * y₁ + x₁ * W.a₁) * hG2
  -- Conclude `v (negAddY - negY x₂ y₂) < 1`.
  have hnegAddY : v (W.toAffine.negAddY x₁ x₂ y₁ ℓ - W.toAffine.negY x₂ y₂) < 1 := by
    have hle : v ((W.toAffine.negAddY x₁ x₂ y₁ ℓ - W.toAffine.negY x₂ y₂) * (x₁ - x₂) ^ 3)
        < v x₁ ^ 3 := by
      rw [key2]
      refine vlt (vlt (vlt (vlt (lt_of_le_of_lt hA2 h_1_a3) ?_) ?_) ?_) ?_
      · rw [Valuation.map_mul]
        calc v x₁ * v (-W.a₃ * W.a₄ + W.a₁ * W.a₆ - 3 * y₂ * W.a₄ - y₂ * W.a₁ * W.a₃
              - 2 * x₂ * y₂ * W.a₂ - x₂ * y₂ * W.a₁ * W.a₁ + 3 * x₂ * x₂ * W.a₃
              + x₂ * x₂ * W.a₁ * W.a₂ + 3 * x₂ * x₂ * y₂ + 4 * x₂ * x₂ * x₂ * W.a₁)
            ≤ v x₁ * 1 := by gcongr
          _ = v x₁ := mul_one _
          _ < v x₁ ^ 3 := h_a_a3
      · rw [Valuation.map_mul]
        calc v y₁ * v (4 * W.a₆ + W.a₃ * W.a₃ + 3 * x₂ * W.a₄ + x₂ * W.a₁ * W.a₃ - x₂ * y₂ * W.a₁
              + 2 * x₂ * x₂ * W.a₂ + x₂ * x₂ * x₂)
            ≤ v y₁ * 1 := by gcongr
          _ = v y₁ := mul_one _
          _ < v x₁ ^ 3 := h_b_a3
      · rw [Valuation.map_mul, Valuation.map_mul]
        calc v x₁ * v y₁ * v (W.a₄ + W.a₁ * W.a₃ + y₂ * W.a₁ + 2 * x₂ * W.a₂ + x₂ * W.a₁ * W.a₁
              + 3 * x₂ * x₂)
            ≤ v x₁ * v y₁ * 1 := by gcongr
          _ = v x₁ * v y₁ := mul_one _
          _ < v x₁ ^ 3 := h_ab_a3
      · rw [Valuation.map_mul, map_pow]
        calc v x₁ ^ 2 * v (-W.a₂ * W.a₃ - 2 * y₂ * W.a₂ - 3 * x₂ * W.a₃ - x₂ * W.a₁ * W.a₂
              - 6 * x₂ * y₂ - 3 * x₂ * x₂ * W.a₁)
            ≤ v x₁ ^ 2 * 1 := by gcongr
          _ = v x₁ ^ 2 := mul_one _
          _ < v x₁ ^ 3 := h_a2_a3
    rw [Valuation.map_mul, hvD3] at hle
    exact lt_of_mul_lt_mul_right (by rw [one_mul]; exact hle) zero_le
  -- `v (addY - y₂) < 1` from the two bounds.
  have haddY : v (W.toAffine.addY x₁ x₂ y₁ ℓ - y₂) < 1 := by
    have heq : W.toAffine.addY x₁ x₂ y₁ ℓ - y₂
        = -(W.toAffine.negAddY x₁ x₂ y₁ ℓ - W.toAffine.negY x₂ y₂)
          - W.a₁ * (W.toAffine.addX x₁ x₂ ℓ - x₂) := by
      simp only [Affine.addY, Affine.negY]; ring
    rw [heq]
    refine v.map_sub_lt ?_ ?_
    · rw [Valuation.map_neg]; exact hnegAddY
    · rw [Valuation.map_mul]
      calc v W.a₁ * v (W.toAffine.addX x₁ x₂ ℓ - x₂)
          ≤ 1 * v (W.toAffine.addX x₁ x₂ ℓ - x₂) := by gcongr; exact valuation_a₁_le_one R W
        _ = v (W.toAffine.addX x₁ x₂ ℓ - x₂) := one_mul _
        _ < 1 := haddX
  -- Assemble via `add_of_X_ne`, `redPt_some_eq` (for `Q`), and the glue lemma.
  have hEqQ : (integralModel R W).toAffine.Equation x₀₂ y₀₂ := by
    rw [← Affine.map_equation (W := (integralModel R W).toAffine)
      (IsFractionRing.injective R K) x₀₂ y₀₂, hx₂, hy₂, hcurve]
    exact h₂.1
  have hnsQ : (reduction R W).toAffine.Nonsingular
      (IsLocalRing.residue R x₀₂) (IsLocalRing.residue R y₀₂) :=
    (Affine.equation_iff_nonsingular).mp (hEqQ.map (IsLocalRing.residue R))
  rw [Affine.Point.add_of_X_ne hx12, redPt_some_eq R W hx₂ hy₂ hnsQ]
  refine redPt_some_of_sub_lt_one R W ?_ ?_ hnsQ
  · rw [hx₂]; exact haddX
  · rw [hy₂]; exact haddY

open Classical in
/-- **`redPt` additivity, integral × kernel case.**  Symmetric to `redPt_add_of_mem_E₁_left`: for an
integral point `P = (x₁, y₁)` (`v x₁ ≤ 1`) and a pole point `Q = (x₂, y₂)` in `E₁(K)` (`1 < v x₂`),
adding `Q` fixes the reduction: `redPt (P + Q) = redPt P`. -/
theorem redPt_add_of_mem_E₁_right (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ y₁ x₂ y₂ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    {x₀₁ y₀₁ : R} (hx₁ : algebraMap R K x₀₁ = x₁) (hy₁ : algebraMap R K y₀₁ = y₁)
    (hvx₁ : valuation K (maximalIdeal R) x₁ ≤ 1)
    (hpole : 1 < valuation K (maximalIdeal R) x₂) :
    redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = redPt R W (.some x₁ y₁ h₁) := by
  rw [add_comm]
  exact redPt_add_of_mem_E₁_left R W hx₁ hy₁ hvx₁ hpole

end WeierstrassCurve
