/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.KernelVerticalReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `redPt` additivity: the reduced-vertical `2`-torsion edge (issue #385, closing #382)

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field `k`, and let
`W : WeierstrassCurve K` have good reduction.  This file proves the last remaining
*reduced-vertical* case of the homomorphism property `redPt (P + Q) = redPt P + redPt Q` of the
point-reduction map: the **`2`-torsion edge**, where the two integral points `P`, `Q` reduce to the
*same* `2`-torsion point of the reduced curve (so `redPt P + redPt Q = 0`, and we must show
`redPt (P + Q) = 0`, i.e. `P + Q ∈ E₁(K)`).

The reduced-vertical *non*-`2`-torsion secant case is already handled by
`redPt_add_of_secant_vertical` (issue #382, via `v (x₁ - x₂) < v (y₁ - y₂)`); the literal vertical
`P + Q = O` by `redPt_add_of_Y_eq`.  At a `2`-torsion reduced point the reduced tangent denominator
`2ȳ + a₁x̄ + a₃` vanishes, so that clean domination hypothesis fails — this is exactly the edge
those lemmas leave open.

## The mechanism: the slope is a pole

At the reduced `2`-torsion point the tangent/secant slope `ℓ` is a **pole** (`1 < v ℓ`):

* its **denominator** `d₀` reduces to `2ȳ + a₁x̄ + a₃ = 0`, so `d₀ ∈ 𝔪`;
* its **numerator** `n₀ ≡ 3x̄² + 2a₂x̄ + a₄ - a₁ȳ = -polynomialX.evalEval x̄ ȳ` is a **unit**:
  since `polynomialY.evalEval x̄ ȳ = 0`, reduced nonsingularity forces
  `polynomialX.evalEval x̄ ȳ ≠ 0`.

Hence `v ℓ = v(n₀)/v(d₀) = 1 / v(d₀) > 1`, and in `addX = ℓ² + a₁ℓ - a₂ - x₁ - x₂` the `ℓ²` term
strictly dominates, giving `1 < v (addX)` and therefore `redPt (P + Q) = 0`.  The `ℓ²`-domination
step is the same as in `redPt_add_of_secant_vertical`.

## Main results

* `WeierstrassCurve.redPt_add_of_reduced_two_torsion_secant` — the secant sub-config (`x₁ ≠ x₂`):
  the secant slope is rewritten as `n₀/d₀` via the divided-difference identity
  `n₀·(x₁-x₂) = (y₁-y₂)·d₀`.
* `WeierstrassCurve.redPt_add_self_of_reduced_two_torsion` — the doubling sub-config (`P = Q`, with
  `P` not `2`-torsion over `K`): the tangent slope is `n₀/d₀` directly.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1, VII.2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum WithZero Multiplicative

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Two shared valuation bricks -/

/-- **The `ℓ²`-domination brick.**  If `P`, `Q` are integral (`v xᵢ ≤ 1`) and the slope `ℓ` has a
pole (`1 < v ℓ`), then the `x`-coordinate `addX = ℓ² + a₁ℓ - a₂ - x₁ - x₂` of the secant/tangent sum
has `1 < v (addX)`, because the leading `ℓ²` term strictly dominates every other term (each of
valuation `≤ v ℓ < (v ℓ)²` or `≤ 1 < (v ℓ)²`).  This is the reduced-vertical secant argument of
`redPt_add_of_secant_vertical`, isolated so both the secant and the doubling `2`-torsion edges reuse
it. -/
private theorem one_lt_valuation_addX_of_one_lt_slope (W : WeierstrassCurve K) [IsIntegral R W]
    {x₁ x₂ ℓ : K} (hx₁ : valuation K (maximalIdeal R) x₁ ≤ 1)
    (hx₂ : valuation K (maximalIdeal R) x₂ ≤ 1)
    (h1ltℓ : 1 < valuation K (maximalIdeal R) ℓ) :
    1 < valuation K (maximalIdeal R) (W.toAffine.addX x₁ x₂ ℓ) := by
  set v : Valuation K ℤᵐ⁰ := valuation K (maximalIdeal R) with hv
  have hℓ2 : v ℓ < (v ℓ) ^ 2 := by
    calc v ℓ = (v ℓ) ^ 1 := (pow_one _).symm
      _ < (v ℓ) ^ 2 := pow_lt_pow_right₀ h1ltℓ (by norm_num)
  have h1ltℓ2 : 1 < (v ℓ) ^ 2 := one_lt_pow₀ h1ltℓ (by norm_num)
  have ha1 : v W.a₁ ≤ 1 := valuation_a₁_le_one R W
  have ha2 : v W.a₂ ≤ 1 := valuation_a₂_le_one R W
  have hva1ℓ : v (W.a₁ * ℓ) < (v ℓ) ^ 2 := by
    rw [v.map_mul]
    calc v W.a₁ * v ℓ ≤ 1 * v ℓ := by gcongr
      _ = v ℓ := one_mul _
      _ < (v ℓ) ^ 2 := hℓ2
  have hva2 : v W.a₂ < (v ℓ) ^ 2 := lt_of_le_of_lt ha2 h1ltℓ2
  have hvx1 : v x₁ < (v ℓ) ^ 2 := lt_of_le_of_lt hx₁ h1ltℓ2
  have hvx2 : v x₂ < (v ℓ) ^ 2 := lt_of_le_of_lt hx₂ h1ltℓ2
  have hvℓ2 : v (ℓ ^ 2) = (v ℓ) ^ 2 := by rw [map_pow]
  have htail : v (W.a₁ * ℓ - W.a₂ - x₁ - x₂) < (v ℓ) ^ 2 :=
    v.map_sub_lt (v.map_sub_lt (v.map_sub_lt hva1ℓ hva2) hvx1) hvx2
  have hsum : W.toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 + (W.a₁ * ℓ - W.a₂ - x₁ - x₂) := by
    simp only [Affine.addX]; ring
  rw [hsum, Valuation.map_add_eq_of_lt_left _ (by rw [hvℓ2]; exact htail), hvℓ2]
  exact h1ltℓ2

/-- **The pole brick.**  If `n₀` is a unit of `R` and `d₀` a nonzero element of the maximal ideal,
then `algebraMap n₀ / algebraMap d₀` has valuation `1 / v(d₀) > 1`.  (`n₀ ∉ 𝔪` has valuation `1`; a
nonzero `d₀ ∈ 𝔪` has valuation strictly between `0` and `1`.) -/
private theorem one_lt_valuation_div {n₀ d₀ : R}
    (hn : IsUnit n₀) (hd : d₀ ∈ IsLocalRing.maximalIdeal R) (hd0 : d₀ ≠ 0) :
    1 < valuation K (maximalIdeal R) (algebraMap R K n₀ / algebraMap R K d₀) := by
  have hn1 : valuation K (maximalIdeal R) (algebraMap R K n₀) = 1 := by
    rw [valuation_eq_one_iff_notMem]; exact IsLocalRing.notMem_maximalIdeal.mpr hn
  have hdlt : valuation K (maximalIdeal R) (algebraMap R K d₀) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) d₀).mpr hd
  have hdne : algebraMap R K d₀ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd0
  have hdpos : 0 < valuation K (maximalIdeal R) (algebraMap R K d₀) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hdne)
  rw [Valuation.map_div, hn1, one_lt_div₀ hdpos]
  exact hdlt

/-! ### The `2`-torsion secant edge -/

open Classical in
/-- **`redPt` additivity, reduced-vertical `2`-torsion secant edge.**  For integral points
`P = (x₁, y₁)`, `Q = (x₂, y₂)` (`v xᵢ ≤ 1`) that are **distinct over `K`** (`x₁ ≠ x₂`) but reduce to
the *same* `2`-torsion point (`residue x₀₁ = residue x₀₂`, `residue y₀₁ = residue y₀₂`, and the
reduced point is vertical: `residue y₀₁ = negY (residue x₀₁) (residue y₀₁)`), the secant slope is a
pole, so `1 < v (addX)` and `redPt (P + Q) = 0`.

The divided-difference identity `n₀·(x₁-x₂) = (y₁-y₂)·d₀` (from subtracting the two Weierstrass
equations) exhibits the secant slope as `n₀/d₀`, whose denominator reduces to the vanishing tangent
denominator `2ȳ + a₁x̄ + a₃` (`d₀ ∈ 𝔪`) and whose numerator reduces to the tangent numerator, a unit
by reduced nonsingularity. -/
theorem redPt_add_of_reduced_two_torsion_secant (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ y₁ x₂ y₂ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    {x₀₁ y₀₁ x₀₂ y₀₂ : R}
    (hx₁ : algebraMap R K x₀₁ = x₁) (hy₁ : algebraMap R K y₀₁ = y₁)
    (hx₂ : algebraMap R K x₀₂ = x₂) (hy₂ : algebraMap R K y₀₂ = y₂)
    (hvx₁ : valuation K (maximalIdeal R) x₁ ≤ 1) (hvx₂ : valuation K (maximalIdeal R) x₂ ≤ 1)
    (hx12 : x₁ ≠ x₂)
    (hxeq : IsLocalRing.residue R x₀₁ = IsLocalRing.residue R x₀₂)
    (hyeq : IsLocalRing.residue R y₀₁ = IsLocalRing.residue R y₀₂)
    (h2t : IsLocalRing.residue R y₀₁
      = (reduction R W).toAffine.negY (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁)) :
    redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 := by
  haveI : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  have hcurve : (integralModel R W).toAffine.map (algebraMap R K) = W.toAffine :=
    baseChange_integralModel_eq R W
  -- divided-difference denominator `d₀` and numerator `n₀`.
  set d₀ : R := y₀₁ + y₀₂ + (integralModel R W).a₁ * x₀₂ + (integralModel R W).a₃ with hd₀
  set n₀ : R := x₀₁ ^ 2 + x₀₁ * x₀₂ + x₀₂ ^ 2 + (integralModel R W).a₂ * (x₀₁ + x₀₂)
    + (integralModel R W).a₄ - (integralModel R W).a₁ * y₀₁ with hn₀
  -- reduced nonsingularity of the common reduced point.
  have hEqP : (integralModel R W).toAffine.Equation x₀₁ y₀₁ := by
    rw [← Affine.map_equation (W := (integralModel R W).toAffine)
      (IsFractionRing.injective R K) x₀₁ y₀₁, hx₁, hy₁, hcurve]; exact h₁.1
  have hnsP : (reduction R W).toAffine.Nonsingular
      (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) :=
    (Affine.equation_iff_nonsingular).mp (hEqP.map (IsLocalRing.residue R))
  -- residue of the denominator vanishes (the reduced point is `2`-torsion).
  have hd_res : IsLocalRing.residue R d₀ = IsLocalRing.residue R y₀₁
      - (reduction R W).toAffine.negY (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) := by
    rw [hd₀]
    simp only [reduction, Affine.negY, map_add, map_mul, map_a₁, map_a₃, ← hxeq, ← hyeq]
    ring
  have hd0res : IsLocalRing.residue R d₀ = 0 := by rw [hd_res]; exact sub_eq_zero.mpr h2t
  have hdmem : d₀ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.residue_eq_zero_iff d₀).mp hd0res
  -- residue of the numerator is `-polynomialX.evalEval`, nonzero by nonsingularity.
  have hPY0 : (reduction R W).toAffine.polynomialY.evalEval
      (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) = 0 := by
    have hval : (reduction R W).toAffine.polynomialY.evalEval
        (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁)
        = IsLocalRing.residue R y₀₁ - (reduction R W).toAffine.negY
            (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) := by
      rw [Affine.evalEval_polynomialY, Affine.negY]; ring
    rw [hval]; exact sub_eq_zero.mpr h2t
  have hPX : (reduction R W).toAffine.polynomialX.evalEval
      (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) ≠ 0 :=
    hnsP.2.resolve_right (not_not.mpr hPY0)
  have hn_res : IsLocalRing.residue R n₀ = -(reduction R W).toAffine.polynomialX.evalEval
      (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) := by
    rw [hn₀, Affine.evalEval_polynomialX]
    simp only [reduction, map_sub, map_add, map_mul, map_pow, map_a₁, map_a₂, map_a₄, ← hxeq]
    ring
  have hnn0 : IsLocalRing.residue R n₀ ≠ 0 := by rw [hn_res]; exact neg_ne_zero.mpr hPX
  have hn_unit : IsUnit n₀ :=
    IsLocalRing.notMem_maximalIdeal.mp
      (fun hmem => hnn0 ((IsLocalRing.residue_eq_zero_iff n₀).mpr hmem))
  -- `algebraMap` forms of `d₀`, `n₀`, and the divided-difference identity over `K`.
  have hd_K : algebraMap R K d₀ = y₁ + y₂ + W.a₁ * x₂ + W.a₃ := by
    rw [hd₀]
    simp only [map_add, map_mul, integralModel_a₁_eq, integralModel_a₃_eq, hx₂, hy₁, hy₂]
  have hn_K : algebraMap R K n₀
      = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁ := by
    rw [hn₀]
    simp only [map_sub, map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₄_eq, hx₁, hx₂, hy₁]
  have key : algebraMap R K n₀ * (x₁ - x₂) = (y₁ - y₂) * algebraMap R K d₀ := by
    rw [hn_K, hd_K]
    linear_combination (W.toAffine.equation_iff' x₂ y₂).mp h₂.1 -
      (W.toAffine.equation_iff' x₁ y₁).mp h₁.1
  -- `d₀ ≠ 0` (else the identity forces the unit `n₀` to vanish).
  have hd0ne : d₀ ≠ 0 := by
    intro h
    rw [h, map_zero, mul_zero] at key
    rcases mul_eq_zero.mp key with hn0 | hx0
    · exact hn_unit.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective R K)).mp hn0)
    · exact hx12 (sub_eq_zero.mp hx0)
  -- the secant slope equals `n₀/d₀`, hence is a pole.
  have hdKne : algebraMap R K d₀ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd0ne
  have hslope : W.toAffine.slope x₁ x₂ y₁ y₂ = algebraMap R K n₀ / algebraMap R K d₀ := by
    rw [Affine.slope_of_X_ne hx12, div_eq_div_iff (sub_ne_zero.mpr hx12) hdKne]
    linear_combination -key
  have h1ltℓ : 1 < valuation K (maximalIdeal R) (W.toAffine.slope x₁ x₂ y₁ y₂) := by
    rw [hslope]; exact one_lt_valuation_div R hn_unit hdmem hd0ne
  -- assemble: `addX` dominates, so `P + Q ∈ E₁`.
  have haddX : 1 < valuation K (maximalIdeal R)
      (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) :=
    one_lt_valuation_addX_of_one_lt_slope R W hvx₁ hvx₂ h1ltℓ
  rw [Affine.Point.add_of_X_ne hx12]
  exact redPt_some_of_one_lt R W haddX

/-! ### The `2`-torsion doubling edge -/

open Classical in
/-- **`redPt` additivity, reduced-vertical `2`-torsion doubling edge.**  For an integral point
`P = (x₁, y₁)` (`v x₁ ≤ 1`) that is **not** `2`-torsion over `K` (`y₁ ≠ negY x₁ y₁`, else
`P + P = O` is `redPt_add_of_Y_eq`) but whose reduction is a `2`-torsion point
(`residue y₀₁ = negY (residue x₀₁) (residue y₀₁)`), the doubling tangent slope is a pole, so
`1 < v (addX)` and `redPt (P + P) = 0`. -/
theorem redPt_add_self_of_reduced_two_torsion (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ y₁ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} {x₀₁ y₀₁ : R}
    (hx₁ : algebraMap R K x₀₁ = x₁) (hy₁ : algebraMap R K y₀₁ = y₁)
    (hvx₁ : valuation K (maximalIdeal R) x₁ ≤ 1)
    (hyK : y₁ ≠ W.toAffine.negY x₁ y₁)
    (h2t : IsLocalRing.residue R y₀₁
      = (reduction R W).toAffine.negY (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁)) :
    redPt R W (.some x₁ y₁ h₁ + .some x₁ y₁ h₁) = 0 := by
  haveI : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  have hcurve : (integralModel R W).toAffine.map (algebraMap R K) = W.toAffine :=
    baseChange_integralModel_eq R W
  -- tangent denominator `d₀` and numerator `n₀`.
  set d₀ : R := y₀₁ + y₀₁ + (integralModel R W).a₁ * x₀₁ + (integralModel R W).a₃ with hd₀
  set n₀ : R := x₀₁ ^ 2 + x₀₁ * x₀₁ + x₀₁ ^ 2 + (integralModel R W).a₂ * (x₀₁ + x₀₁)
    + (integralModel R W).a₄ - (integralModel R W).a₁ * y₀₁ with hn₀
  have hEqP : (integralModel R W).toAffine.Equation x₀₁ y₀₁ := by
    rw [← Affine.map_equation (W := (integralModel R W).toAffine)
      (IsFractionRing.injective R K) x₀₁ y₀₁, hx₁, hy₁, hcurve]; exact h₁.1
  have hnsP : (reduction R W).toAffine.Nonsingular
      (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) :=
    (Affine.equation_iff_nonsingular).mp (hEqP.map (IsLocalRing.residue R))
  have hd_res : IsLocalRing.residue R d₀ = IsLocalRing.residue R y₀₁
      - (reduction R W).toAffine.negY (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) := by
    rw [hd₀]
    simp only [reduction, Affine.negY, map_add, map_mul, map_a₁, map_a₃]
    ring
  have hd0res : IsLocalRing.residue R d₀ = 0 := by rw [hd_res]; exact sub_eq_zero.mpr h2t
  have hdmem : d₀ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.residue_eq_zero_iff d₀).mp hd0res
  have hPY0 : (reduction R W).toAffine.polynomialY.evalEval
      (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) = 0 := by
    have hval : (reduction R W).toAffine.polynomialY.evalEval
        (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁)
        = IsLocalRing.residue R y₀₁ - (reduction R W).toAffine.negY
            (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) := by
      rw [Affine.evalEval_polynomialY, Affine.negY]; ring
    rw [hval]; exact sub_eq_zero.mpr h2t
  have hPX : (reduction R W).toAffine.polynomialX.evalEval
      (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) ≠ 0 :=
    hnsP.2.resolve_right (not_not.mpr hPY0)
  have hn_res : IsLocalRing.residue R n₀ = -(reduction R W).toAffine.polynomialX.evalEval
      (IsLocalRing.residue R x₀₁) (IsLocalRing.residue R y₀₁) := by
    rw [hn₀, Affine.evalEval_polynomialX]
    simp only [reduction, map_sub, map_add, map_mul, map_pow, map_a₁, map_a₂, map_a₄]
    ring
  have hnn0 : IsLocalRing.residue R n₀ ≠ 0 := by rw [hn_res]; exact neg_ne_zero.mpr hPX
  have hn_unit : IsUnit n₀ :=
    IsLocalRing.notMem_maximalIdeal.mp
      (fun hmem => hnn0 ((IsLocalRing.residue_eq_zero_iff n₀).mpr hmem))
  -- `algebraMap` forms; the tangent slope equals `n₀/d₀` directly (`slope_of_Y_ne`).
  have hd_K : algebraMap R K d₀ = y₁ - W.toAffine.negY x₁ y₁ := by
    rw [hd₀, Affine.negY]
    simp only [map_add, map_mul, integralModel_a₁_eq, integralModel_a₃_eq, hx₁, hy₁]
    ring
  have hn_K : algebraMap R K n₀
      = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ := by
    rw [hn₀]
    simp only [map_sub, map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₄_eq, hx₁, hy₁]
    ring
  have hd0ne : d₀ ≠ 0 := by
    intro h
    apply hyK
    have : algebraMap R K d₀ = 0 := by rw [h, map_zero]
    rw [hd_K, sub_eq_zero] at this
    exact this
  have hdKne : algebraMap R K d₀ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd0ne
  have hslope : W.toAffine.slope x₁ x₁ y₁ y₁ = algebraMap R K n₀ / algebraMap R K d₀ := by
    rw [Affine.slope_of_Y_ne rfl hyK, hn_K, hd_K]
  have h1ltℓ : 1 < valuation K (maximalIdeal R) (W.toAffine.slope x₁ x₁ y₁ y₁) := by
    rw [hslope]; exact one_lt_valuation_div R hn_unit hdmem hd0ne
  have haddX : 1 < valuation K (maximalIdeal R)
      (W.toAffine.addX x₁ x₁ (W.toAffine.slope x₁ x₁ y₁ y₁)) :=
    one_lt_valuation_addX_of_one_lt_slope R W hvx₁ hvx₁ h1ltℓ
  rw [Affine.Point.add_self_of_Y_ne hyK]
  exact redPt_some_of_one_lt R W haddX

end WeierstrassCurve
