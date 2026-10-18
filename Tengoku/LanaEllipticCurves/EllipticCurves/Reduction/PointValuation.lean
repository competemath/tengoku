/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.NewtonPolygon
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Reduction
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation of affine point coordinates over a DVR and the `E₁(K)` predicate

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field `k`, and let
`W : WeierstrassCurve K` be given by an **integral** Weierstrass equation (`IsIntegral R W`, so all
coefficients `aᵢ` lie in `R`).  Following Silverman (AEC VII.2 Prop 2.1) we analyse the valuations
of the coordinates of an affine point `P = (x, y)` on `W`, and define the predicate that `P`
**reduces to the origin** — the membership relation of the kernel of reduction `E₁(K)`.

⚠️ **This sentence called it the *"eventual"* membership relation, and it stopped being eventual.**
`E₁ R W : AddSubgroup (W⁄K).Point` exists (`EllipticCurves.Reduction.KernelAddClosure`, #367) and
`mem_E₁` is `P ∈ E₁ R W ↔ ReducesToZero R W P`, proved by `Iff.rfl` — so the predicate defined here
is not a stand-in for the eventual relation, it **is** it, definitionally.  The subgroup structure
is what was eventual, and it arrived.

We use the multiplicative `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`-valued valuation
`valuation K (maximalIdeal R)` (exactly the one used by Mathlib's `EllipticCurve/Reduction.lean`),
where for `r : R` one has `v (algebraMap R K r) ≤ 1`, and `v z < 1` means `z` reduces into the
maximal ideal `𝔪`.

## Main results

* `valuation_pow_two_eq_pow_three_of_one_lt` — the **Newton-polygon dichotomy**: if `P = (x, y)`
  lies on an integral `W` and `x` has a pole (`1 < v x`), then `1 < v y` and `(v y) ^ 2 = (v x) ^ 3`
  (i.e. `2·ord y = 3·ord x`).
* `valuation_lt_of_one_lt` — in the pole regime `v x < v y`, hence the local parameter `z = -x/y`
  has `v (-x/y) < 1` (`valuation_neg_x_div_y_lt_one`), i.e. `z` reduces into `𝔪`.
* `WeierstrassCurve.ReducesToZero` — the predicate `P ∈ E₁(K)` (`P` reduces to the origin): either
  `P = 0`, or `P = some x y` with `1 < v x`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1, VII.2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum WithZero Multiplicative

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Valuations of the coefficients of an integral model -/

/-- Every coefficient of an integral Weierstrass model has valuation `≤ 1`. -/
theorem valuation_a₁_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₁ ≤ 1 := by
  rw [← integralModel_a₁_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₂_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₂ ≤ 1 := by
  rw [← integralModel_a₂_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₃_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₃ ≤ 1 := by
  rw [← integralModel_a₃_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₄_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₄ ≤ 1 := by
  rw [← integralModel_a₄_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₆_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₆ ≤ 1 := by
  rw [← integralModel_a₆_eq R W]; exact valuation_le_one (maximalIdeal R) _

/-! ### The Newton-polygon dichotomy for a point with a pole -/

/-- **Newton-polygon dichotomy (Silverman AEC VII.2 Prop 2.1).**  If `P = (x, y)` lies on an
integral Weierstrass curve `W` and the `x`-coordinate has a pole (`1 < v x`), then the
`y`-coordinate also has a pole and `(v y) ^ 2 = (v x) ^ 3` — the multiplicative form of
`2·ord y = 3·ord x`.

This is `WeierstrassCurve.valuation_pow_two_eq_pow_three_of_valuation_le_one`
(`EllipticCurves.NewtonPolygon`) specialised to the adic valuation of the maximal ideal of `R`; the
coefficient bounds it takes as hypotheses are exactly `valuation_a₁_le_one`, …,
`valuation_a₆_le_one` above.  The general statement holds for an arbitrary value group, because
the argument only ever compares integer powers of `v x` and `v y` and never halves. -/
theorem valuation_pow_two_eq_pow_three_of_one_lt (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} (heqn : W.toAffine.Equation x y) (hx : 1 < valuation K (maximalIdeal R) x) :
    1 < valuation K (maximalIdeal R) y ∧
      (valuation K (maximalIdeal R) y) ^ 2 = (valuation K (maximalIdeal R) x) ^ 3 :=
  valuation_pow_two_eq_pow_three_of_valuation_le_one _ W (valuation_a₁_le_one R W)
    (valuation_a₂_le_one R W) (valuation_a₃_le_one R W) (valuation_a₄_le_one R W)
    (valuation_a₆_le_one R W) heqn hx

/-- In the pole regime `1 < v x`, the `y`-pole strictly dominates: `v x < v y`. -/
theorem valuation_lt_of_one_lt (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} (heqn : W.toAffine.Equation x y) (hx : 1 < valuation K (maximalIdeal R) x) :
    valuation K (maximalIdeal R) x < valuation K (maximalIdeal R) y := by
  obtain ⟨hb1, hrel⟩ := valuation_pow_two_eq_pow_three_of_one_lt R W heqn hx
  set a : ℤᵐ⁰ := valuation K (maximalIdeal R) x
  set b : ℤᵐ⁰ := valuation K (maximalIdeal R) y
  -- `b ^ 2 = a ^ 3 > a ^ 2`, so `b > a`.
  have ha2a3 : a ^ 2 < a ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
  have hab : a ^ 2 < b ^ 2 := by rw [hrel]; exact ha2a3
  exact lt_of_pow_lt_pow_left₀ 2 zero_le hab

/-- The local parameter `z = -x/y` of a point with a pole reduces into the maximal ideal:
`v (-x / y) < 1`. -/
theorem valuation_neg_x_div_y_lt_one (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} (heqn : W.toAffine.Equation x y) (hx : 1 < valuation K (maximalIdeal R) x) :
    valuation K (maximalIdeal R) (-x / y) < 1 := by
  have hlt := valuation_lt_of_one_lt R W heqn hx
  set v : Valuation K ℤᵐ⁰ := valuation K (maximalIdeal R) with hv
  have hvx_pos : 0 < v x := lt_trans one_pos hx
  have hvy_pos : 0 < v y := lt_trans hvx_pos hlt
  rw [v.map_div, v.map_neg]
  exact (div_lt_one₀ hvy_pos).mpr hlt

/-! ### The `E₁(K)` predicate: points reducing to the origin -/

/-- A point `P` of `W` over `K` **reduces to the origin** (`E₁(K)` membership, definitionally: see
`mem_E₁` in `EllipticCurves.Reduction.KernelAddClosure`): either
`P = 0`, or `P = some x y` whose `x`-coordinate has a pole (`1 < v x`).  For a point on an integral
model this is equivalent to reducing to `Õ` on the reduced curve (Silverman AEC VII.2).

⚠️ **`[IsIntegral R W]` is unused in the elaborated term and is kept on purpose** (`#1277`,
`nolint unusedArguments`; `#1272`'s Part C reached the same verdict).  The predicate *means*
"reduces to `Õ` on an integral model", the instance is that model, and the whole API around it
(`reducesToZero_zero` and the rest) takes it — so dropping it here would change a type and split
the predicate from its own theory. -/
@[nolint unusedArguments]
def ReducesToZero (W : WeierstrassCurve K) [IsIntegral R W] : W.toAffine.Point → Prop
  | .zero => True
  | .some x _ _ => 1 < valuation K (maximalIdeal R) x

@[simp] theorem reducesToZero_zero (W : WeierstrassCurve K) [IsIntegral R W] :
    ReducesToZero R W .zero := trivial

theorem reducesToZero_some_iff (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} {h : W.toAffine.Nonsingular x y} :
    ReducesToZero R W (.some x y h) ↔ 1 < valuation K (maximalIdeal R) x := Iff.rfl

/-- An integral point (`v x ≤ 1`) does not reduce to the origin. -/
theorem not_reducesToZero_of_valuation_le_one (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} {h : W.toAffine.Nonsingular x y} (hx : valuation K (maximalIdeal R) x ≤ 1) :
    ¬ ReducesToZero R W (.some x y h) := by
  rw [reducesToZero_some_iff]; exact not_lt.mpr hx

end WeierstrassCurve
