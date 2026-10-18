/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GenuineLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Vieta factorisation of the substituted `z`-cubic

Following Silverman AEC IV.1, Theorem 1.1, the chord process substitutes the line
`w = λ z + ν` into the Weierstrass relation, giving a cubic in `z` with leading coefficient
`A = W.formalGroupLead` (a unit) and subleading coefficient `B = W.formalGroupSub`.  Its two known
roots are the uniformisers `z₁ = X 0`, `z₂ = X 1` (`formalCubicResidual_root_zero` / `_one`).  By
Vieta the third root is `z₃' = W.formalThirdRoot = -(B·A⁻¹) - z₁ - z₂`.

The **main result** `WeierstrassCurve.formalCubicResidual_root_thirdRoot` proves that this Vieta
third root really is a root of the substituted cubic.  This is the crux of #314: the third
intersection point of the chord with the curve is pinned down algebraically, which is the
prerequisite for identifying the genuine `(z, w)`-plane law with the Laurent formal group law.

## Main results

* `WeierstrassCurve.formalCubicResidual_root_thirdRoot` : `z₃'` is a root of the substituted cubic.

## Implementation notes

The Vieta argument needs to cancel a factor `z₂ - z₁ = X 1 - X 0`.  In `MvPowerSeries (Fin 2) R`
this element is **not** a unit (its constant coefficient is `0`), but it is a *non-zero-divisor*
(regular): this is `MvPowerSeries.eq_zero_of_mul_X_one_sub_X_zero_eq_zero`, proved by a coefficient
shift and induction on the `X 0`-degree.  The core algebraic Vieta step is packaged as the
ring-theoretic lemma `vieta_root_of_regular`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries

/-! ### An abstract Vieta step over a commutative ring

If a cubic (given via its divided-difference factorisation) has two roots `x`, `y` with `x - y`
regular, unit leading coefficient `A` (`A · a = 1`) and subleading coefficient `B`, then the Vieta
third root `z = -(B·a) - x - y` is again a root. -/

/-- **Abstract Vieta third root.** Let `F : T → T` be a cubic through its divided difference:
`F u - F v = (u - v) · (A·(u² + u·v + v²) + B·(u + v) + Cc)`.  If `x, y` are roots, `A · a = 1`,
`z = -(B·a) - x - y`, and multiplication by `x - y` is injective, then `F z = 0`. -/
theorem vieta_root_of_regular {T : Type*} [CommRing T] (F : T → T) (A B Cc x y z a : T)
    (hdiff : ∀ u v : T, F u - F v = (u - v) * (A * (u ^ 2 + u * v + v ^ 2) + B * (u + v) + Cc))
    (hFx : F x = 0) (hFy : F y = 0) (hA : A * a = 1) (hz : z = -(B * a) - x - y)
    (hreg : ∀ c : T, (x - y) * c = 0 → c = 0) : F z = 0 := by
  -- The divided-difference "quotient" evaluated at `(x, y)` vanishes.
  have hGxy : A * (x ^ 2 + x * y + y ^ 2) + B * (x + y) + Cc = 0 := by
    refine hreg _ ?_
    have h := hdiff x y
    rw [hFx, hFy] at h
    linear_combination -h
  -- Evaluate `F z` via the divided difference at `(z, x)`.
  have hFz : F z = (z - x) * (A * (z ^ 2 + z * x + x ^ 2) + B * (z + x) + Cc) := by
    have h := hdiff z x
    rw [hFx] at h
    linear_combination h
  -- The quadratic factor at `(z, x)` factors through `(z - y)` using `hGxy`.
  have hfactor : A * (z ^ 2 + z * x + x ^ 2) + B * (z + x) + Cc
      = (z - y) * (A * (z + x + y) + B) := by
    have h2 : A * (z ^ 2 + z * x + x ^ 2) + B * (z + x) + Cc
        = (z - y) * (A * (z + x + y) + B) + (A * (x ^ 2 + x * y + y ^ 2) + B * (x + y) + Cc) := by
      ring
    rw [h2, hGxy, add_zero]
  -- The remaining linear factor vanishes by the Vieta definition of `z` and `A · a = 1`.
  have hlin : A * (z + x + y) + B = 0 := by
    rw [hz]; linear_combination -B * hA
  rw [hFz, hfactor, hlin, mul_zero, mul_zero]

/-! ### `X 1 - X 0` is a non-zero-divisor in `MvPowerSeries (Fin 2) R` -/

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

/-- Multiplying by the variable `X s` shifts the coefficient index by `single s 1`. -/
private theorem coeff_mul_X_shift (φ : MvPowerSeries (Fin 2) R) (s : Fin 2)
    (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff (m + Finsupp.single s 1) (φ * X s) = MvPowerSeries.coeff m φ := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_add_mul_monomial, mul_one]

/-- **`X 1 - X 0` is a non-zero-divisor.**  If `(X 1 - X 0) · c = 0` then `c = 0`.  Proved by a
coefficient shift and induction on the `X 0`-degree; this holds over an arbitrary commutative ring
(where `X 1 - X 0` is regular but not a unit). -/
theorem eq_zero_of_mul_X_one_sub_X_zero_eq_zero (c : MvPowerSeries (Fin 2) R)
    (h : (X 1 - X 0) * c = 0) : c = 0 := by
  have hcomm : c * X 1 = c * X 0 := by linear_combination h
  refine MvPowerSeries.ext fun d => ?_
  rw [map_zero]
  -- Prove `coeff d c = 0` by strong induction on `d 0`.
  suffices H : ∀ n (d : Fin 2 →₀ ℕ), d 0 = n → MvPowerSeries.coeff d c = 0 by
    exact H (d 0) d rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro d hd
    by_cases hd0 : d 0 = 0
    · -- Base: `d 0 = 0`.  Then `coeff d c = coeff (d + e₁) (c * X 0) = 0`.
      have hk := congrArg (MvPowerSeries.coeff (d + Finsupp.single 1 1)) hcomm
      rw [coeff_mul_X_shift] at hk
      have hrhs : MvPowerSeries.coeff (d + Finsupp.single 1 1) (c * X 0) = 0 := by
        refine MvPowerSeries.X_dvd_iff.mp ⟨c, by ring⟩ _ ?_
        rw [Finsupp.add_apply, hd0, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_add]
      exact hk.trans hrhs
    · -- Step: `d 0 ≥ 1`.  Write `d = m + e₀` and use the inductive hypothesis at `m + e₁`.
      have hpos : 1 ≤ d 0 := Nat.one_le_iff_ne_zero.mpr hd0
      have hle : Finsupp.single (0 : Fin 2) 1 ≤ d := Finsupp.single_le_iff.mpr hpos
      set m := d - Finsupp.single (0 : Fin 2) 1 with hm
      have hdeq : m + Finsupp.single (0 : Fin 2) 1 = d := tsub_add_cancel_of_le hle
      have hk := congrArg
        (MvPowerSeries.coeff (m + Finsupp.single 0 1 + Finsupp.single 1 1)) hcomm
      rw [coeff_mul_X_shift, show
          m + Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1
            = m + Finsupp.single 1 1 + Finsupp.single 0 1 from add_right_comm _ _ _,
        coeff_mul_X_shift] at hk
      rw [hdeq] at hk
      have hd0m : d 0 = m 0 + 1 := by
        rw [← hdeq, Finsupp.add_apply, Finsupp.single_eq_same]
      have hmc : MvPowerSeries.coeff (m + Finsupp.single 1 1) c = 0 := by
        refine ih (m 0) (by omega) (m + Finsupp.single 1 1) ?_
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero]
      exact hk.trans hmc

end MvPowerSeries

/-! ### The Vieta third root is a root of the substituted cubic -/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The constant coefficient of `λ = formalWDividedDiff` vanishes. -/
private theorem constantCoeff_formalWDividedDiff' :
    MvPowerSeries.constantCoeff W.formalWDividedDiff = 0 :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
    (le_trans (by exact_mod_cast one_le_two) W.two_le_order_formalWDividedDiff)

/-- The constant coefficient of the cubic's leading coefficient `A` is `1`. -/
private theorem constantCoeff_formalGroupLead' :
    MvPowerSeries.constantCoeff W.formalGroupLead = 1 := by
  rw [formalGroupLead]
  simp only [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, map_one,
    W.constantCoeff_formalWDividedDiff']
  ring

/-- **Vieta third root is a root of the substituted cubic.**  The Vieta third root
`z₃' = W.formalThirdRoot = -(B·A⁻¹) - z₁ - z₂` solves the substituted `z`-cubic, exactly like the
two known roots `z₁ = X 0`, `z₂ = X 1` (`formalCubicResidual_root_zero` / `_one`).  This is the
`z`-cubic Vieta factorisation crux of #314. -/
theorem formalCubicResidual_root_thirdRoot :
    W.formalThirdRoot ^ 3
      + (C W.a₁ * W.formalThirdRoot + C W.a₂ * W.formalThirdRoot ^ 2)
          * (W.formalWDividedDiff * W.formalThirdRoot + W.formalGroupNu)
      + (C W.a₃ + C W.a₄ * W.formalThirdRoot)
          * (W.formalWDividedDiff * W.formalThirdRoot + W.formalGroupNu) ^ 2
      + C W.a₆ * (W.formalWDividedDiff * W.formalThirdRoot + W.formalGroupNu) ^ 3
      - (W.formalWDividedDiff * W.formalThirdRoot + W.formalGroupNu) = 0 := by
  have hA : W.formalGroupLead * invOfUnit W.formalGroupLead 1 = 1 :=
    MvPowerSeries.mul_invOfUnit W.formalGroupLead 1
      (by rw [W.constantCoeff_formalGroupLead', Units.val_one])
  refine vieta_root_of_regular
    (F := fun u => u ^ 3
      + (C W.a₁ * u + C W.a₂ * u ^ 2) * (W.formalWDividedDiff * u + W.formalGroupNu)
      + (C W.a₃ + C W.a₄ * u) * (W.formalWDividedDiff * u + W.formalGroupNu) ^ 2
      + C W.a₆ * (W.formalWDividedDiff * u + W.formalGroupNu) ^ 3
      - (W.formalWDividedDiff * u + W.formalGroupNu))
    (A := W.formalGroupLead) (B := W.formalGroupSub)
    (Cc := C W.a₁ * W.formalGroupNu
      + 2 * C W.a₃ * W.formalWDividedDiff * W.formalGroupNu
      + C W.a₄ * W.formalGroupNu ^ 2
      + 3 * C W.a₆ * W.formalWDividedDiff * W.formalGroupNu ^ 2
      - W.formalWDividedDiff)
    (x := X 0) (y := X 1) (z := W.formalThirdRoot)
    (a := invOfUnit W.formalGroupLead 1)
    ?_ W.formalCubicResidual_root_zero W.formalCubicResidual_root_one hA rfl ?_
  · -- Divided-difference factorisation of the cubic (pure ring identity).
    intro u v
    simp only [formalGroupLead, formalGroupSub]
    ring
  · -- Regularity of `x - y = X 0 - X 1`.
    intro c hc
    refine MvPowerSeries.eq_zero_of_mul_X_one_sub_X_zero_eq_zero c ?_
    linear_combination -hc

end WeierstrassCurve
