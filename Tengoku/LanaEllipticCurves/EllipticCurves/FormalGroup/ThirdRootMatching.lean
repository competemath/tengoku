/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GeometricMatching
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.CubicFactorisation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Third-root matching: the coordinate-change image of `(x₃, Y)` is the Vieta third root

`EllipticCurves.FormalGroup.GeometricMatching` reduced the identification
`embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent` to the single relation

`(K4)  x₃ · P = Z`,  where `Z = φ(z₃')` is the `(z, w)`-plane Vieta third root and `P = μ·Z + ν_L`
is the chord `w`-value (`φ = HahnSeries.embedDoubleLaurent`).

This file discharges the whole geometric half of `(K4)`, reducing it to a single **regularity**
hypothesis on the coordinate differences.  The idea (Silverman AEC IV.1, Theorem 1.1) is the
projective-linear change of coordinates `z = -x/y`, `w = -1/y`.  Writing `Y := λ·x₃ + ν` for the
secant `y`-value at the third point, the change of coordinates sends `(x₃, Y)` to
`(z_c, w_c) = (-x₃·Y⁻¹, -Y⁻¹)`.  We prove:

* `isUnit_thirdSecantY` : `Y = λ·x₃ + ν` is a unit (so `z_c := -x₃·Y⁻¹` is well-defined);
* the chord bridges give `Y·(μ·z_c + ν_L) = -1` and `Y·z_c = -x₃`, whence
  `zPlaneCurve_thirdPoint` : `z_c` is a root of the substituted `z`-cubic `F`;
* `vieta_third_root_unique` : the abstract uniqueness twin of `vieta_root_of_regular` — a cubic
  through its divided difference has a unique Vieta third root once the relevant differences are
  regular;
* `embedDoubleLaurent_formalGroupZW_of_regular` : combining the four roots `z₁, z₂, Z, z_c` of `F`
  with the uniqueness lemma forces `z_c = Z`, hence `(K1)` `Z·Y = -x₃`, hence `(K4)`, hence the
  identification — **conditional only on regularity of `z_c - z₁` and `z_c - z₂`** (the third
  difference `z₁ - z₂ = biZ₂ - biZ₁` is already a unit, `isUnit_biZ₂_sub_biZ₁`).

The remaining regularity of `z_c - z_i` (equivalently `x₃ - x_i`, since
`z_c - z_i = -ν·(x₃ - x_i)·(Y·y_i)⁻¹` with `ν, Y, y_i` units) is **false over a general commutative
ring** — the leading coefficient of `x₃ - x_i` is `-2`, not a unit in e.g. characteristic `2`.  It
holds when `(R⸨X⸩)⸨X⸩` is a domain, and the general case follows by base change from the universal
curve over `ℤ[a₁, …, a₆]` (a characteristic-`0` domain).  That transfer is the sole remaining step
for #314; everything geometric is discharged here.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries
open scoped LaurentSeries

/-! ### An abstract Vieta third-root uniqueness lemma -/

/-- **Abstract Vieta third-root uniqueness.** Companion to `vieta_root_of_regular`: if a cubic
`F` (presented through its divided difference) has roots `x`, `y`, and a further root `w`, with
`x - y`, `w - x`, `w - y` all regular (left-cancellable) and unit leading coefficient `A`
(`A · a = 1`), then `w` is forced to equal the Vieta third root `-(B·a) - x - y`. -/
theorem vieta_third_root_unique {T : Type*} [CommRing T] (F : T → T) (A B Cc x y w a : T)
    (hdiff : ∀ u v : T, F u - F v = (u - v) * (A * (u ^ 2 + u * v + v ^ 2) + B * (u + v) + Cc))
    (hFx : F x = 0) (hFy : F y = 0) (hFw : F w = 0) (hA : A * a = 1)
    (hregxy : ∀ c : T, (x - y) * c = 0 → c = 0)
    (hregwx : ∀ c : T, (w - x) * c = 0 → c = 0)
    (hregwy : ∀ c : T, (w - y) * c = 0 → c = 0) :
    w = -(B * a) - x - y := by
  have hGxy : A * (x ^ 2 + x * y + y ^ 2) + B * (x + y) + Cc = 0 := by
    refine hregxy _ ?_
    have h := hdiff x y; rw [hFx, hFy] at h; linear_combination -h
  have hGwx : A * (w ^ 2 + w * x + x ^ 2) + B * (w + x) + Cc = 0 := by
    refine hregwx _ ?_
    have h := hdiff w x; rw [hFw, hFx] at h; linear_combination -h
  have hlin : A * (w + x + y) + B = 0 := by
    refine hregwy _ ?_
    linear_combination hGwx - hGxy
  linear_combination a * hlin - (w + x + y) * hA

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The secant `y`-value `Y = λ·x₃ + ν` at the third point is a unit -/

/-- **The secant `y`-value at the third point is a unit.** `Y = λ·x₃ + ν` has `z₂`-order `0` with
leading coefficient the unit `-y(z₁) - a₁·x(z₁)`, hence is a unit of `(R⸨X⸩)⸨X⸩`. Concretely
`Y = -y₃ - a₁·x₃ - a₃` (the definition of `y₃`), and `-y₃` dominates. -/
theorem isUnit_thirdSecantY :
    IsUnit (W.formalLambda * W.formalXThree + W.formalNu) := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton _
  · -- Rewrite `Y = λ·x₃ + ν` as `-y₃ - a₁·x₃ - a₃` (the definition of `y₃`).
    have hYeq : W.formalLambda * W.formalXThree + W.formalNu
        = -W.formalYThree - HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
          - HahnSeries.C (HahnSeries.C W.a₃) := by
      unfold formalYThree
      ring
    rw [hYeq]
    set Yout := -W.formalYThree - HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
        - HahnSeries.C (HahnSeries.C W.a₃) with hYoutdef
    -- The inner `z₁`-series `L = -y(z₁) - a₁·x(z₁) - a₃` is a unit of `R⸨X⸩` (inner order `-3`,
    -- dominated by `-y(z₁)` whose leading coefficient is the unit `-(-1) = 1`).
    have hLunit : IsUnit (-W.formalY - HahnSeries.C W.a₁ * W.formalX - HahnSeries.C W.a₃) := by
      have hLbelow : ∀ g : ℤ, g < -3 →
          (-W.formalY - HahnSeries.C W.a₁ * W.formalX - HahnSeries.C W.a₃).coeff g = 0 := by
        intro g hg
        rw [HahnSeries.coeff_sub, HahnSeries.coeff_sub, HahnSeries.coeff_neg,
          W.coeff_formalY_of_lt hg, HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero,
          W.coeff_formalX_of_lt (by omega), HahnSeries.C_apply,
          HahnSeries.coeff_single_of_ne (show g ≠ 0 by omega)]
        ring
      have hL3 :
          (-W.formalY - HahnSeries.C W.a₁ * W.formalX - HahnSeries.C W.a₃).coeff (-3) = 1 := by
        rw [HahnSeries.coeff_sub, HahnSeries.coeff_sub, HahnSeries.coeff_neg,
          W.coeff_formalY_neg_three, HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero,
          W.coeff_formalX_of_lt (show (-3 : ℤ) < -2 by norm_num), HahnSeries.C_apply,
          HahnSeries.coeff_single_of_ne (show (-3 : ℤ) ≠ 0 by norm_num)]
        ring
      have hne : (-W.formalY - HahnSeries.C W.a₁ * W.formalX - HahnSeries.C W.a₃) ≠ 0 :=
        fun h => by
          rw [h, HahnSeries.coeff_zero] at hL3
          exact one_ne_zero hL3.symm
      have hle : (-W.formalY - HahnSeries.C W.a₁ * W.formalX - HahnSeries.C W.a₃).order ≤ -3 :=
        HahnSeries.order_le_of_coeff_ne_zero (by rw [hL3]; exact one_ne_zero)
      have hge : (-3 : ℤ) ≤
          (-W.formalY - HahnSeries.C W.a₁ * W.formalX - HahnSeries.C W.a₃).order := by
        by_contra hlt
        exact HahnSeries.coeff_order_eq_zero.not.2 hne (hLbelow _ (not_le.mp hlt))
      have horder : (-W.formalY - HahnSeries.C W.a₁ * W.formalX - HahnSeries.C W.a₃).order = -3 :=
        le_antisymm hle hge
      refine HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ ?_
      · rw [HahnSeries.leadingCoeff_eq, horder, hL3]; exact isUnit_one
      · rw [horder]; exact AddGroup.isAddUnit _
    -- `y₃` and `x₃` have `z₂`-order `0` with leading coefficients `y(z₁)`, `x(z₁)`.
    have hy3_0 : W.formalYThree.coeff 0 = W.formalY := by
      have hne' : W.formalYThree ≠ 0 :=
        HahnSeries.orderTop_ne_top.mp (by rw [W.orderTop_formalYThree]; exact WithTop.zero_ne_top)
      have hord : W.formalYThree.order = 0 := by
        have h : (W.formalYThree.order : WithTop ℤ) = (0 : WithTop ℤ) := by
          rw [HahnSeries.order_eq_orderTop_of_ne_zero hne', W.orderTop_formalYThree]
        exact_mod_cast h
      rw [show (0 : ℤ) = W.formalYThree.order from hord.symm, ← HahnSeries.leadingCoeff_eq,
        W.leadingCoeff_formalYThree]
    have hx3_0 : W.formalXThree.coeff 0 = W.formalX := by
      have hne' : W.formalXThree ≠ 0 :=
        HahnSeries.orderTop_ne_top.mp (by rw [W.orderTop_formalXThree]; exact WithTop.zero_ne_top)
      have hord : W.formalXThree.order = 0 := by
        have h : (W.formalXThree.order : WithTop ℤ) = (0 : WithTop ℤ) := by
          rw [HahnSeries.order_eq_orderTop_of_ne_zero hne', W.orderTop_formalXThree]
        exact_mod_cast h
      rw [show (0 : ℤ) = W.formalXThree.order from hord.symm, ← HahnSeries.leadingCoeff_eq,
        W.leadingCoeff_formalXThree]
    -- `Yout.coeff 0 = L`, computed summand by summand.
    have e1 : (HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree).coeff 0
        = HahnSeries.C W.a₁ * W.formalX := by
      rw [HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero, hx3_0]
    have e2 : (HahnSeries.C (HahnSeries.C W.a₃) : (R⸨X⸩)⸨X⸩).coeff 0 = HahnSeries.C W.a₃ := by
      rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]
    have hcoeff0 : Yout.coeff 0
        = -W.formalY - HahnSeries.C W.a₁ * W.formalX - HahnSeries.C W.a₃ := by
      rw [hYoutdef, HahnSeries.coeff_sub, HahnSeries.coeff_sub, HahnSeries.coeff_neg, hy3_0, e1, e2]
    -- `Yout.coeff g = 0` for `g < 0`.
    have hbelow : ∀ g : ℤ, g < 0 → Yout.coeff g = 0 := by
      intro g hg
      have f1 : (HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree).coeff g = 0 := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero,
          HahnSeries.coeff_eq_zero_of_lt_orderTop
            (by rw [W.orderTop_formalXThree]; exact_mod_cast hg), mul_zero]
      have f2 : (HahnSeries.C (HahnSeries.C W.a₃) : (R⸨X⸩)⸨X⸩).coeff g = 0 := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (show g ≠ 0 by omega)]
      rw [hYoutdef, HahnSeries.coeff_sub, HahnSeries.coeff_sub, HahnSeries.coeff_neg,
        HahnSeries.coeff_eq_zero_of_lt_orderTop
          (by rw [W.orderTop_formalYThree]; exact_mod_cast hg), f1, f2]
      ring
    -- `Yout` has `z₂`-order `0` and unit leading coefficient `L`, hence is a unit.
    have hne : Yout ≠ 0 := fun h => by
      rw [h, HahnSeries.coeff_zero] at hcoeff0
      exact hLunit.ne_zero hcoeff0.symm
    have hle : Yout.order ≤ 0 :=
      HahnSeries.order_le_of_coeff_ne_zero (by rw [hcoeff0]; exact hLunit.ne_zero)
    have hge : (0 : ℤ) ≤ Yout.order := by
      by_contra hlt
      exact HahnSeries.coeff_order_eq_zero.not.2 hne (hbelow _ (not_le.mp hlt))
    have horder : Yout.order = 0 := le_antisymm hle hge
    refine HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ ?_
    · rw [HahnSeries.leadingCoeff_eq, horder, hcoeff0]; exact hLunit
    · rw [horder]; exact AddGroup.isAddUnit _

/-! ### The coordinate-change image of `(x₃, Y)` is a root of the `z`-cubic -/

/-- The secant `y`-value `Y = λ·x₃ + ν` at the third point (the `(x, y)`-plane `y`-coordinate of
the third intersection, before the curve's negation). -/
noncomputable def secantY : (R⸨X⸩)⸨X⸩ := W.formalLambda * W.formalXThree + W.formalNu

/-- The coordinate-change image `z_c = -x₃·Y⁻¹` of the third point under `z = -x/y`. -/
noncomputable def coordChangeZ : (R⸨X⸩)⸨X⸩ :=
  -W.formalXThree * Ring.inverse (W.secantY)

/-- `Y · z_c = -x₃` (defining property of the coordinate-change `z`-value). -/
private theorem secantY_mul_coordChangeZ :
    W.secantY * W.coordChangeZ = -W.formalXThree := by
  have hY : W.secantY * Ring.inverse W.secantY = 1 :=
    Ring.mul_inverse_cancel _ W.isUnit_thirdSecantY
  rw [coordChangeZ]
  linear_combination (-W.formalXThree) * hY

/-- `Y · (μ·z_c + ν_L) = -1`: the chord `w`-value at `z_c` is `-Y⁻¹`.  Uses the two linear bridges
`μ = ν_L·λ` and `ν_L·ν = -1`. -/
private theorem secantY_mul_chord_coordChangeZ :
    W.secantY * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.coordChangeZ
        + HahnSeries.embedDoubleLaurent W.formalGroupNu) = -1 := by
  have hzc := W.secantY_mul_coordChangeZ
  have hslope := W.formalWDividedDiff_image_eq
  have hint := W.formalGroupNu_image_mul_formalNu
  rw [secantY] at hzc ⊢
  -- Y·(μ z_c + ν_L) = μ·(Y z_c) + ν_L·Y = μ·(-x₃) + ν_L·(λx₃+ν)
  --                 = -ν_L·λ·x₃ + ν_L·λ·x₃ + ν_L·ν = ν_L·ν = -1.
  linear_combination HahnSeries.embedDoubleLaurent W.formalWDividedDiff * hzc
    - W.formalXThree * hslope + hint

/-- **The coordinate-change image `z_c` is a root of the substituted `z`-cubic.** The cubic `F` is
the `z`-plane Weierstrass equation with the chord `w = μ z + ν_L` substituted. Since `(x₃, Y)` lies
on the `(x, y)`-curve (`weierstrass_thirdInt`), its coordinate-change image `(z_c, -Y⁻¹)` lies on
the `z`-plane curve; and `-Y⁻¹ = μ z_c + ν_L` by the bridges, so `z_c` solves the substituted
cubic. -/
private theorem zPlaneCurve_thirdPoint :
    W.coordChangeZ ^ 3
        + (HahnSeries.C (HahnSeries.C W.a₁) * W.coordChangeZ
            + HahnSeries.C (HahnSeries.C W.a₂) * W.coordChangeZ ^ 2)
          * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.coordChangeZ
              + HahnSeries.embedDoubleLaurent W.formalGroupNu)
        + (HahnSeries.C (HahnSeries.C W.a₃) + HahnSeries.C (HahnSeries.C W.a₄) * W.coordChangeZ)
          * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.coordChangeZ
              + HahnSeries.embedDoubleLaurent W.formalGroupNu) ^ 2
        + HahnSeries.C (HahnSeries.C W.a₆)
          * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.coordChangeZ
              + HahnSeries.embedDoubleLaurent W.formalGroupNu) ^ 3
        - (HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.coordChangeZ
            + HahnSeries.embedDoubleLaurent W.formalGroupNu) = 0 := by
  -- The two chord bridges (with `secantY` unfolded to `λ·x₃ + ν`).
  have hzc0 := W.secantY_mul_coordChangeZ
  have hchord0 := W.secantY_mul_chord_coordChangeZ
  rw [secantY] at hzc0 hchord0
  have hw := W.weierstrass_thirdInt
  obtain ⟨u, hu⟩ := W.isUnit_thirdSecantY.pow 3
  set Y := W.formalLambda * W.formalXThree + W.formalNu with hY
  set zc := W.coordChangeZ with hzcd
  set P := HahnSeries.embedDoubleLaurent W.formalWDividedDiff * zc
      + HahnSeries.embedDoubleLaurent W.formalGroupNu with hPd
  -- `Y³·(each term of the cubic)`, collapsed via `Y·zc = -x₃` and `Y·P = -1`.
  have t1 : Y ^ 3 * zc ^ 3 = -W.formalXThree ^ 3 := by
    have e : Y ^ 3 * zc ^ 3 = (Y * zc) ^ 3 := by ring
    rw [e, hzc0]
    ring
  have t2 : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₁) * zc * P)
      = HahnSeries.C (HahnSeries.C W.a₁) * Y * W.formalXThree := by
    have e : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₁) * zc * P)
        = HahnSeries.C (HahnSeries.C W.a₁) * (Y * zc) * (Y * P) * Y := by ring
    rw [e, hzc0, hchord0]
    ring
  have t3 : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₂) * zc ^ 2 * P)
      = -(HahnSeries.C (HahnSeries.C W.a₂) * W.formalXThree ^ 2) := by
    have e : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₂) * zc ^ 2 * P)
        = HahnSeries.C (HahnSeries.C W.a₂) * (Y * zc) ^ 2 * (Y * P) := by ring
    rw [e, hzc0, hchord0]
    ring
  have t4 : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₃) * P ^ 2)
      = HahnSeries.C (HahnSeries.C W.a₃) * Y := by
    have e : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₃) * P ^ 2)
        = HahnSeries.C (HahnSeries.C W.a₃) * Y * (Y * P) ^ 2 := by ring
    rw [e, hchord0]
    ring
  have t5 : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₄) * zc * P ^ 2)
      = -(HahnSeries.C (HahnSeries.C W.a₄) * W.formalXThree) := by
    have e : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₄) * zc * P ^ 2)
        = HahnSeries.C (HahnSeries.C W.a₄) * (Y * zc) * (Y * P) ^ 2 := by ring
    rw [e, hzc0, hchord0]
    ring
  have t6 : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₆) * P ^ 3)
      = -HahnSeries.C (HahnSeries.C W.a₆) := by
    have e : Y ^ 3 * (HahnSeries.C (HahnSeries.C W.a₆) * P ^ 3)
        = HahnSeries.C (HahnSeries.C W.a₆) * (Y * P) ^ 3 := by ring
    rw [e, hchord0]
    ring
  have t7 : Y ^ 3 * P = -Y ^ 2 := by
    have e : Y ^ 3 * P = Y ^ 2 * (Y * P) := by ring
    rw [e, hchord0]
    ring
  -- `Y³` is a unit, so cancelling it from `Y³·F(zc) = 0` gives `F(zc) = 0`.
  refine (Units.mul_right_eq_zero u).mp ?_
  rw [hu]
  linear_combination t1 + t2 + t3 + t4 + t5 + t6 - t7 + hw

/-! ### The identification, conditional on regularity of the coordinate differences -/

/-- **`(K1)` from the third-root match.** If `z_c = Z` (the coordinate-change image of `(x₃, Y)` is
the Vieta third root), then `(K1)` `Z·Y = -x₃` holds. -/
private theorem thirdPoint_K1_of_match
    (hzcZ : W.coordChangeZ = HahnSeries.embedDoubleLaurent W.formalThirdRoot) :
    HahnSeries.embedDoubleLaurent W.formalThirdRoot
        * (W.formalLambda * W.formalXThree + W.formalNu) = -W.formalXThree := by
  have h := W.secantY_mul_coordChangeZ
  rw [secantY, hzcZ] at h
  linear_combination h

/-- **The identification from regularity of the coordinate differences.** Given that both
`z_c - z₁` and `z_c - z₂` are regular (left-cancellable) in `(R⸨X⸩)⸨X⸩`, the `(z, w)`- and Laurent
formal group laws agree. (`z₁ - z₂ = biZ₂ - biZ₁` is already a unit, `isUnit_biZ₂_sub_biZ₁`.)

The Vieta third root `Z = φ(z₃')` and the coordinate-change image `z_c = -x₃·Y⁻¹` are both roots of
the substituted `z`-cubic, so third-root uniqueness (`vieta_third_root_unique`) forces `z_c = Z`,
whence `(K1)` and thence `(K4)`. -/
theorem embedDoubleLaurent_formalGroupZW_of_regular
    (hregwx : ∀ c : (R⸨X⸩)⸨X⸩, (W.coordChangeZ - W.biZ₁) * c = 0 → c = 0)
    (hregwy : ∀ c : (R⸨X⸩)⸨X⸩, (W.coordChangeZ - W.biZ₂) * c = 0 → c = 0) :
    HahnSeries.embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent := by
  -- The substituted `z`-cubic `F`.
  set μ := HahnSeries.embedDoubleLaurent W.formalWDividedDiff with hμ
  set νL := HahnSeries.embedDoubleLaurent W.formalGroupNu with hνL
  set A := HahnSeries.embedDoubleLaurent W.formalGroupLead with hA
  set B := HahnSeries.embedDoubleLaurent W.formalGroupSub with hB
  set F : (R⸨X⸩)⸨X⸩ → (R⸨X⸩)⸨X⸩ := fun u =>
    u ^ 3
      + (HahnSeries.C (HahnSeries.C W.a₁) * u + HahnSeries.C (HahnSeries.C W.a₂) * u ^ 2)
        * (μ * u + νL)
      + (HahnSeries.C (HahnSeries.C W.a₃) + HahnSeries.C (HahnSeries.C W.a₄) * u)
        * (μ * u + νL) ^ 2
      + HahnSeries.C (HahnSeries.C W.a₆) * (μ * u + νL) ^ 3
      - (μ * u + νL) with hF
  set Cc : (R⸨X⸩)⸨X⸩ :=
    HahnSeries.C (HahnSeries.C W.a₁) * νL
      + 2 * HahnSeries.C (HahnSeries.C W.a₃) * μ * νL
      + HahnSeries.C (HahnSeries.C W.a₄) * νL ^ 2
      + 3 * HahnSeries.C (HahnSeries.C W.a₆) * μ * νL ^ 2 - μ with hCc
  -- The divided-difference presentation of `F`.
  have hdiff : ∀ u v : (R⸨X⸩)⸨X⸩,
      F u - F v = (u - v) * (A * (u ^ 2 + u * v + v ^ 2) + B * (u + v) + Cc) := by
    intro u v
    simp only [hF, hA, hB, hCc, W.embedDoubleLaurent_formalGroupLead,
      W.embedDoubleLaurent_formalGroupSub, hμ, hνL]
    ring
  -- `A · Ring.inverse A = 1`.
  have hAinv : A * Ring.inverse A = 1 := by
    rw [hA]; exact W.embedDoubleLaurent_formalGroupLead_mul_inverse
  -- The four roots of `F`.
  have hFz1 : F W.biZ₁ = 0 := by
    simp only [hF, hμ, hνL]; rw [W.chordW_biZ₁]; exact W.zPlaneCurve_biZ₁
  have hFz2 : F W.biZ₂ = 0 := by
    simp only [hF, hμ, hνL]; rw [W.chordW_biZ₂]; exact W.zPlaneCurve_biZ₂
  have hFZ : F (HahnSeries.embedDoubleLaurent W.formalThirdRoot) = 0 := by
    simp only [hF, hμ, hνL]; exact W.zPlaneCurve_thirdRoot
  have hFzc : F W.coordChangeZ = 0 := by
    simp only [hF, hμ, hνL]; exact W.zPlaneCurve_thirdPoint
  -- `z₁ - z₂` is regular (it is a unit).
  have hregxy : ∀ c : (R⸨X⸩)⸨X⸩, (W.biZ₁ - W.biZ₂) * c = 0 → c = 0 := by
    intro c hc
    obtain ⟨u, hu⟩ := W.isUnit_biZ₂_sub_biZ₁
    refine (Units.mul_right_eq_zero (-u)).mp ?_
    rw [Units.val_neg, hu]; linear_combination hc
  -- `z_c = Z` by third-root uniqueness.
  have hmatch : W.coordChangeZ = -(B * Ring.inverse A) - W.biZ₁ - W.biZ₂ :=
    vieta_third_root_unique F A B Cc W.biZ₁ W.biZ₂ W.coordChangeZ (Ring.inverse A)
      hdiff hFz1 hFz2 hFzc hAinv hregxy hregwx hregwy
  have hZeq : HahnSeries.embedDoubleLaurent W.formalThirdRoot
      = -(B * Ring.inverse A) - W.biZ₁ - W.biZ₂ := by
    rw [hB, hA]; exact W.embedDoubleLaurent_formalThirdRoot
  have hzcZ : W.coordChangeZ = HahnSeries.embedDoubleLaurent W.formalThirdRoot := by
    rw [hmatch, hZeq]
  -- `(K1)`, then `(K4)`, then the identification.
  have hK1 := W.thirdPoint_K1_of_match hzcZ
  have hslope := W.formalWDividedDiff_image_eq
  have hint := W.formalGroupNu_image_mul_formalNu
  refine W.embedDoubleLaurent_formalGroupZW_of_K4 ?_
  -- `(K4)` `x₃·(μ Z + ν_L) = Z` from `(K1)` and the two bridges.
  linear_combination HahnSeries.embedDoubleLaurent W.formalGroupNu * hK1
    + (W.formalXThree * HahnSeries.embedDoubleLaurent W.formalThirdRoot) * hslope
    - (HahnSeries.embedDoubleLaurent W.formalThirdRoot) * hint

end WeierstrassCurve
