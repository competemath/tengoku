/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.PointValuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The set-level reduction map on points of a Weierstrass curve over a DVR

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field
`k = ResidueField R`, and let `W : WeierstrassCurve K` have **good reduction**
(`HasGoodReduction R W`, hence a minimal integral model whose reduced curve `reduction R W` over
`k` is an elliptic curve).

Building on the coordinate-valuation analysis of `EllipticCurves/Reduction/PointValuation.lean`
(Silverman AEC VII.2 Prop 2.1), we define the **set-level reduction map on points**
`redPt : (W⁄K).Point → (reduction R W).Point` and prove it is well defined:

* an **integral point** `(x, y)` (with `v x ≤ 1`, so both coordinates lift to `R`) maps to the
  residues of its coordinates, which — because the reduced curve is elliptic and hence smooth
  everywhere — automatically satisfy the reduced curve's `Nonsingular` predicate;
* every **non-integral point** (`1 < v x`, i.e. a pole) maps to the origin `Õ = 0`, as does `O`.

The kernel `redPt ⁻¹' {0}` is exactly the `ReducesToZero` (`E₁(K)`) predicate; see
`redPt_eq_zero_iff`.  The group-homomorphism property and the identification `E₁(K) ≅ Ê(𝔪)` are
proved in sibling files, not here: `WeierstrassCurve.redPt_add` / `redHom` / `E₁_eq_ker`
(`EllipticCurves/Reduction/ReductionHom.lean`) and `WeierstrassCurve.E₁AddEquiv`
(`EllipticCurves/Reduction/KernelFormalGroupIso.lean`).  ⚠️ This sentence used to say they were
*"deferred to the sibling issues"*; both landed a week after it was written.

## Main definitions

* `WeierstrassCurve.redPt` — the reduction map on points.

## Main results

* `WeierstrassCurve.valuation_y_le_one_of_le_one` — the integral branch of the dichotomy: on an
  integral model, `v x ≤ 1` forces `v y ≤ 1`.
* `WeierstrassCurve.reduction_nonsingular_of_le_one` — the well-definedness / nonsingularity
  obligation: the residues of an integral point's coordinates are nonsingular on the reduced curve.
* `WeierstrassCurve.redPt_zero`, `redPt_some_of_one_lt`, `redPt_eq_zero_iff` — the basic API.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1, VII.2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing
  WithZero Multiplicative

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Integrality of both coordinates -/

/-- On an integral model, if the `x`-coordinate of a point is integral (`v x ≤ 1`), then so is the
`y`-coordinate.  This is the "integral" branch of the Newton-polygon dichotomy (the complement of
`valuation_pow_two_eq_pow_three_of_one_lt`): if `1 < v y` then the term `y²` would strictly dominate
the Weierstrass equation, forcing `v (LHS) = (v y)² > 1`, contradicting `v (RHS) ≤ 1`. -/
theorem valuation_y_le_one_of_le_one (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} (heqn : W.toAffine.Equation x y) (hx : valuation K (maximalIdeal R) x ≤ 1) :
    valuation K (maximalIdeal R) y ≤ 1 := by
  set v : Valuation K ℤᵐ⁰ := valuation K (maximalIdeal R) with hv
  set a : ℤᵐ⁰ := v x with ha
  set b : ℤᵐ⁰ := v y with hb
  by_contra hcon
  rw [not_le] at hcon  -- hcon : 1 < b
  have ha1 : v W.a₁ ≤ 1 := valuation_a₁_le_one R W
  have ha2 : v W.a₂ ≤ 1 := valuation_a₂_le_one R W
  have ha3 : v W.a₃ ≤ 1 := valuation_a₃_le_one R W
  have ha4 : v W.a₄ ≤ 1 := valuation_a₄_le_one R W
  have ha6 : v W.a₆ ≤ 1 := valuation_a₆_le_one R W
  rw [Affine.equation_iff] at heqn
  -- The right-hand side has valuation `≤ 1`: every term does (all `aᵢ` and `x` are integral).
  have hRHS_le : v (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) ≤ 1 := by
    refine v.map_add_le (v.map_add_le (v.map_add_le ?_ ?_) ?_) ha6
    · rw [map_pow]
      calc a ^ 3 ≤ 1 ^ 3 := by gcongr; exact zero_le
        _ = 1 := one_pow 3
    · rw [map_mul, map_pow]
      calc v W.a₂ * a ^ 2 ≤ 1 * 1 ^ 2 := by gcongr; exact zero_le
        _ = 1 := by norm_num
    · rw [map_mul]
      calc v W.a₄ * a ≤ 1 * 1 := by gcongr
        _ = 1 := by norm_num
  -- On the left, `y²` strictly dominates: `v (a₁xy + a₃y) ≤ b < b²`.
  have hb0 : (0 : ℤᵐ⁰) < b := zero_lt_one.trans hcon
  have hb2 : (1 : ℤᵐ⁰) < b ^ 2 := one_lt_pow₀ hcon (by norm_num)
  have hva1xy : v (W.a₁ * x * y) ≤ b := by
    rw [map_mul, map_mul]
    calc v W.a₁ * a * b ≤ 1 * 1 * b := by gcongr
      _ = b := by rw [one_mul, one_mul]
  have hva3y : v (W.a₃ * y) ≤ b := by
    rw [map_mul]
    calc v W.a₃ * b ≤ 1 * b := by gcongr
      _ = b := one_mul b
  set T : K := W.a₁ * x * y + W.a₃ * y with hT
  have hvT : v T ≤ b := le_trans (v.map_add _ _) (max_le hva1xy hva3y)
  have hb_lt_b2 : b < b ^ 2 := by
    have h := pow_lt_pow_right₀ hcon (by norm_num : (1 : ℕ) < 2)
    rwa [pow_one] at h
  have hvT_lt : v T < b ^ 2 := lt_of_le_of_lt hvT hb_lt_b2
  have hLHS : v (y ^ 2 + T) = b ^ 2 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hvT_lt), map_pow]
  have hsum : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y ^ 2 + T := by rw [hT]; ring
  have hb2_le : b ^ 2 ≤ 1 := by rw [← hLHS, ← hsum, heqn]; exact hRHS_le
  exact absurd (lt_of_lt_of_le hb2 hb2_le) (lt_irrefl _)

/-! ### Well-definedness of reduction on the good-reduction locus -/

/-- **Well-definedness of point reduction.**  If `W` has good reduction and `(x, y)` is an integral
point (`v x ≤ 1`, hence `v y ≤ 1` too), let `x₀, y₀ : R` be integral lifts of `x, y`.  Then the
residues `x₀ mod 𝔪`, `y₀ mod 𝔪` satisfy the reduced curve's `Nonsingular` predicate.

The Weierstrass equation transfers from `K` down to the integral model (both coordinates are
integral) and then to the residue field via the ring homomorphism `residue R`.  Because the reduced
curve is an elliptic curve (good reduction ⟹ `IsElliptic`), it is smooth everywhere, so any point on
it satisfying the equation is automatically nonsingular. -/
theorem reduction_nonsingular_of_le_one (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x y : K} (heqn : W.toAffine.Equation x y) (hx : valuation K (maximalIdeal R) x ≤ 1) :
    (reduction R W).toAffine.Nonsingular
      (residue R (exists_lift_of_le_one hx).choose)
      (residue R (exists_lift_of_le_one
        (valuation_y_le_one_of_le_one R W heqn hx)).choose) := by
  set x₀ : R := (exists_lift_of_le_one hx).choose with hx₀def
  have hx₀ : algebraMap R K x₀ = x := (exists_lift_of_le_one hx).choose_spec
  set y₀ : R := (exists_lift_of_le_one
    (valuation_y_le_one_of_le_one R W heqn hx)).choose with hy₀def
  have hy₀ : algebraMap R K y₀ = y :=
    (exists_lift_of_le_one (valuation_y_le_one_of_le_one R W heqn hx)).choose_spec
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hcurve : (integralModel R W).toAffine.map (algebraMap R K) = W.toAffine :=
    baseChange_integralModel_eq R W
  -- The equation holds on the integral model over `R`.
  have hInt : (integralModel R W).toAffine.Equation x₀ y₀ := by
    rw [← Affine.map_equation (W := (integralModel R W).toAffine) hinj x₀ y₀, hx₀, hy₀, hcurve]
    exact heqn
  -- Push it down to the residue field; `reduction R W = (integralModel R W).map (residue R)`.
  have hEq : (reduction R W).toAffine.Equation (residue R x₀) (residue R y₀) :=
    hInt.map (residue R)
  -- The reduced curve is elliptic, so `Equation ↔ Nonsingular`.
  haveI : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  exact (Affine.equation_iff_nonsingular (W := (reduction R W).toAffine)).mp hEq

/-! ### The reduction map on points -/

open Classical in
/-- The **set-level reduction map on points** `E(K) → Ẽ(k)` for a Weierstrass curve `W` with good
reduction over the DVR `R`.  The origin and every point with a pole (`1 < v x`, i.e. not reducing
integrally) map to the origin `Õ`; an integral point maps to the residues of its coordinates. -/
noncomputable def redPt (W : WeierstrassCurve K) [HasGoodReduction R W] :
    W.toAffine.Point → (reduction R W).toAffine.Point
  | .zero => .zero
  | .some x _ h =>
    if hx : valuation K (maximalIdeal R) x ≤ 1 then
      .some _ _ (reduction_nonsingular_of_le_one R W h.1 hx)
    else .zero

@[simp]
theorem redPt_zero (W : WeierstrassCurve K) [HasGoodReduction R W] :
    redPt R W .zero = 0 := rfl

/-- On the integral branch (`v x ≤ 1`), the reduction map sends `(x, y)` to the residues of its
integral lifts `x₀, y₀ : R`.  This is the defining equation of `redPt` on integral points. -/
theorem redPt_some_of_le_one (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x y : K} {h : W.toAffine.Nonsingular x y} (hx : valuation K (maximalIdeal R) x ≤ 1) :
    redPt R W (.some x y h) = .some _ _ (reduction_nonsingular_of_le_one R W h.1 hx) :=
  dite_eq_left hx

/-- A non-integral point (`x` has a pole, `1 < v x`) reduces to the origin. -/
theorem redPt_some_of_one_lt (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x y : K} {h : W.toAffine.Nonsingular x y} (hx : 1 < valuation K (maximalIdeal R) x) :
    redPt R W (.some x y h) = 0 := by
  have : redPt R W (.some x y h) = .zero := dite_eq_right (not_le.mpr hx)
  rw [this]; rfl

/-- The reduction map sends a point to the origin exactly when it reduces to the origin, i.e. its
preimage of `0` is the `E₁(K)` predicate `ReducesToZero`. -/
theorem redPt_eq_zero_iff (W : WeierstrassCurve K) [HasGoodReduction R W]
    (P : W.toAffine.Point) : redPt R W P = 0 ↔ ReducesToZero R W P := by
  cases P with
  | zero => exact iff_of_true (redPt_zero R W) trivial
  | some x y h =>
    rw [reducesToZero_some_iff]
    by_cases hx : valuation K (maximalIdeal R) x ≤ 1
    · have hp : redPt R W (.some x y h) = .some _ _ (reduction_nonsingular_of_le_one R W h.1 hx) :=
        dite_eq_left hx
      rw [hp]
      exact iff_of_false (Affine.Point.some_ne_zero _) (not_lt.mpr hx)
    · have hn : redPt R W (.some x y h) = .zero := dite_eq_right hx
      rw [hn]
      exact iff_of_true rfl (not_le.mp hx)

/-! ### Compatibility with negation

Reduction commutes with negation.  On the reduced curve, negation is again the slope-free formula
`negY`, and `residue` (a ring homomorphism) intertwines the integral-model `negY` with the reduced
`negY` via `WeierstrassCurve.Affine.map_negY`.  This is the first (and easy) half of the
homomorphism property `redPt (P + Q) = redPt P + redPt Q`; the additive half genuinely requires the
formal group (Silverman AEC VII.2.2). -/

/-- The `E₁(K)` predicate only sees the `x`-coordinate, which negation fixes, so it is closed under
negation: `-P` reduces to the origin iff `P` does. -/
theorem reducesToZero_neg (W : WeierstrassCurve K) [IsIntegral R W] (P : W.toAffine.Point) :
    ReducesToZero R W (-P) ↔ ReducesToZero R W P := by
  cases P with
  | zero => exact Iff.rfl
  | some x y h => rw [Affine.Point.neg_some]; exact Iff.rfl

/-- The reduction of an integral point in terms of **any** integral lifts `x₀, y₀ : R` of its
coordinates.  Since `algebraMap R K` is injective the lift is unique, so this is independent of the
choice and identifies `redPt` with the residues of the lifts.  A convenient lift-agnostic form of
`redPt_some_of_le_one`. -/
theorem redPt_some_eq (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x y : K} {h : W.toAffine.Nonsingular x y} {x₀ y₀ : R}
    (hx₀ : algebraMap R K x₀ = x) (hy₀ : algebraMap R K y₀ = y)
    (hns : (reduction R W).toAffine.Nonsingular (residue R x₀) (residue R y₀)) :
    redPt R W (.some x y h) = .some (residue R x₀) (residue R y₀) hns := by
  have hx : valuation K (maximalIdeal R) x ≤ 1 := hx₀ ▸ valuation_le_one (maximalIdeal R) x₀
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have ex : (exists_lift_of_le_one hx).choose = x₀ :=
    hinj (by rw [(exists_lift_of_le_one hx).choose_spec, hx₀])
  have ey : (exists_lift_of_le_one (valuation_y_le_one_of_le_one R W h.1 hx)).choose = y₀ :=
    hinj (by
      rw [(exists_lift_of_le_one (valuation_y_le_one_of_le_one R W h.1 hx)).choose_spec, hy₀])
  rw [redPt_some_of_le_one R W hx]
  simp only [ex, ey]

/-- **Reduction commutes with negation:** `redPt (-P) = -(redPt P)`.  On the pole branch both sides
are `0`; on the integral branch it reduces to
`residue (negY x₀ y₀) = negY (residue x₀) (residue y₀)` on the reduced curve, which is
`WeierstrassCurve.Affine.map_negY` for the ring homomorphism `residue R`.  This is the first (easy)
half of the homomorphism property of `redPt`. -/
theorem redPt_neg (W : WeierstrassCurve K) [HasGoodReduction R W] (P : W.toAffine.Point) :
    redPt R W (-P) = - redPt R W P := by
  cases P with
  | zero => rfl
  | some x y h =>
    by_cases hx : valuation K (maximalIdeal R) x ≤ 1
    · -- Integral branch: choose any lifts `x₀, y₀ : R` of `x, y`.
      obtain ⟨x₀, hx₀⟩ := exists_lift_of_le_one hx
      obtain ⟨y₀, hy₀⟩ := exists_lift_of_le_one (valuation_y_le_one_of_le_one R W h.1 hx)
      have hcurve : (integralModel R W).toAffine.map (algebraMap R K) = W.toAffine :=
        baseChange_integralModel_eq R W
      -- `negY x₀ y₀` on the integral model is a lift of `negY x y`, the `y`-coordinate of `-P`.
      have hnegY : algebraMap R K ((integralModel R W).toAffine.negY x₀ y₀)
          = W.toAffine.negY x y := by
        rw [← Affine.map_negY (algebraMap R K), hcurve, hx₀, hy₀]
      -- Nonsingularity of the reduced coordinates of `P` (`Equation` transfers K → R → k, and the
      -- reduced curve is elliptic hence smooth).
      have hnsP : (reduction R W).toAffine.Nonsingular (residue R x₀) (residue R y₀) := by
        have hInt : (integralModel R W).toAffine.Equation x₀ y₀ := by
          rw [← Affine.map_equation (W := (integralModel R W).toAffine)
            (IsFractionRing.injective R K) x₀ y₀, hx₀, hy₀, hcurve]
          exact h.1
        haveI : (reduction R W).IsElliptic :=
          (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
        exact (Affine.equation_iff_nonsingular).mp (hInt.map (residue R))
      -- Reduced `negY`: `residue (negY x₀ y₀) = negY (residue x₀) (residue y₀)`.
      have hmap : residue R ((integralModel R W).toAffine.negY x₀ y₀)
          = (reduction R W).toAffine.negY (residue R x₀) (residue R y₀) :=
        Affine.map_negY (residue R) x₀ y₀
      -- Nonsingularity of the reduced coordinates of `-P`.
      have hnsNegP : (reduction R W).toAffine.Nonsingular (residue R x₀)
          (residue R ((integralModel R W).toAffine.negY x₀ y₀)) := by
        rw [hmap]; exact (Affine.nonsingular_neg ..).mpr hnsP
      rw [Affine.Point.neg_some, redPt_some_eq R W hx₀ hnegY hnsNegP,
        redPt_some_eq R W hx₀ hy₀ hnsP, Affine.Point.neg_some]
      simp only [hmap]
    · -- Pole branch: both sides are `0`.
      rw [Affine.Point.neg_some,
        redPt_some_of_one_lt R W (not_le.mp hx), redPt_some_of_one_lt R W (not_le.mp hx),
        Affine.Point.neg_zero]

end WeierstrassCurve
