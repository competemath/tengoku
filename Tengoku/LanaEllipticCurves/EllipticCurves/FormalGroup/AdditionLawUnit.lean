/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.AdditionLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `IsUnit (formalYThree)`: the analytic core of the Weierstrass formal group law

This file proves that the third `y`-coordinate `y₃ = W.formalYThree ∈ R⸨z₁⸩⸨z₂⸩` of the
Weierstrass addition law (constructed in `EllipticCurves.FormalGroup.AdditionLaw`) is a **unit**.
This is the analytic heart of the formal group law (Silverman, *The Arithmetic of Elliptic
Curves*, IV.1, Theorem 1.1): it is what makes the formal group series `F_E := -x₃·y₃⁻¹`
well-defined.

## Strategy

Everything is a `z₂`-order (outer-grading) computation in the iterated Laurent ring
`R⸨z₁⸩⸨z₂⸩`, with `z₂`-coefficients lying in `R⸨z₁⸩ = R⸨X⸩`. Write `X₁ := W.formalX`,
`Y₁ := W.formalY ∈ R⸨X⸩` (these are `W.biX₁.coeff 0`, `W.biY₁.coeff 0`).

The denominator `d := x₂ - x₁` is a unit of `z₂`-order `-2` with leading coefficient `1`, so its
inverse `d⁻¹` has `z₂`-order `2`. The slope `λ = (y₂ - y₁)·d⁻¹` therefore has `z₂`-order `-1`.
We compute the **principal part** of `λ` explicitly,
`Λ := z₂⁻¹·(-1) + z₂·(-X₁) + z₂²·(-Y₁ - a₁X₁)`, by showing `n - Λ·d` (where `n := y₂ - y₁`) has
`z₂`-order `≥ 1`, whence `λ - Λ = (n - Λ·d)·d⁻¹` has `z₂`-order `≥ 3`. Reducing every product to
`single`-multiplications (`coeff_single_mul`), all coefficients we need come out by hand, with the
higher-order corrections killed by the order bound. Finally

`y₃.coeff g = 0` for `g < 0` and `y₃.coeff 0 = Y₁`,

so `y₃` has `z₂`-order `0` with leading coefficient the unit `Y₁ = W.formalY`, and is a unit by
`HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder`.

## Main results

* `WeierstrassCurve.isUnit_formalYThree` : `IsUnit W.formalYThree`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### `formalY` is a unit of `R⸨X⸩` -/

/-- The coordinate series `y(z)` is a unit of `R⸨X⸩` (from `y·w = -1`). -/
theorem isUnit_formalY : IsUnit W.formalY :=
  IsUnit.of_mul_eq_one _ (by rw [mul_neg, W.formalY_mul_coe_formalW, neg_neg])

/-! ### Constant `z₂`-coefficients of `x₁, y₁` and the coefficients of `y₂` -/

/-- The order-`0` `z₂`-coefficient of `x₁ = x(z₁)` is `x(z₁) = W.formalX`. -/
theorem coeff_biX₁_zero : W.biX₁.coeff 0 = W.formalX := by
  rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_single_same]

/-- The order-`0` `z₂`-coefficient of `y₁ = y(z₁)` is `y(z₁) = W.formalY`. -/
theorem coeff_biY₁_zero : W.biY₁.coeff 0 = W.formalY := by
  rw [biY₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_single_same]

/-- The series `y₁ = y(z₁)` is supported in `z₂`-degree `0` only. -/
theorem coeff_biY₁_of_ne {g : ℤ} (h : g ≠ 0) : W.biY₁.coeff g = 0 := by
  rw [biY₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

/-- The `z₂`-coefficients of `y₂ = y(z₂)`: the `z₁`-constant coefficient `C (y(z)-coeff)`. -/
theorem coeff_biY₂ (g : ℤ) : W.biY₂.coeff g = HahnSeries.C (W.formalY.coeff g) := by
  rw [biY₂, cLaurentRingHom, HahnSeries.mapRingHom_apply, HahnSeries.map_coeff]

/-! ### Closed forms for the `z₂`-coefficients of `d = x₂ - x₁` and `n = y₂ - y₁` -/

private lemma coeff_d_neg_one : (W.biX₂ - W.biX₁).coeff (-1) = -HahnSeries.C W.a₁ := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, coeff_formalX_neg_one, W.coeff_biX₁_of_ne (by norm_num),
    sub_zero, map_neg]

private lemma coeff_d_zero :
    (W.biX₂ - W.biX₁).coeff 0 = -HahnSeries.C W.a₂ - W.formalX := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, coeff_formalX_zero, W.coeff_biX₁_zero, map_neg]

private lemma coeff_d_one : (W.biX₂ - W.biX₁).coeff 1 = -HahnSeries.C W.a₃ := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, coeff_formalX_one, W.coeff_biX₁_of_ne (by norm_num),
    sub_zero, map_neg]

private lemma coeff_n_neg_three : (W.biY₂ - W.biY₁).coeff (-3) = -1 := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, coeff_formalY_neg_three, W.coeff_biY₁_of_ne (by norm_num),
    sub_zero, map_neg, map_one]

private lemma coeff_n_neg_two : (W.biY₂ - W.biY₁).coeff (-2) = HahnSeries.C W.a₁ := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, coeff_formalY_neg_two, W.coeff_biY₁_of_ne (by norm_num),
    sub_zero]

private lemma coeff_n_neg_one : (W.biY₂ - W.biY₁).coeff (-1) = HahnSeries.C W.a₂ := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, coeff_formalY_neg_one, W.coeff_biY₁_of_ne (by norm_num),
    sub_zero]

private lemma coeff_n_zero :
    (W.biY₂ - W.biY₁).coeff 0 = HahnSeries.C W.a₃ - W.formalY := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, coeff_formalY_zero, W.coeff_biY₁_zero]

private lemma coeff_n_of_lt {g : ℤ} (hg : g < -3) : (W.biY₂ - W.biY₁).coeff g = 0 := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, W.coeff_formalY_of_lt hg, map_zero,
    W.coeff_biY₁_of_ne (by omega), sub_zero]

/-! ### The order and inverse-order of `d = x₂ - x₁` -/

private lemma orderTop_d [Nontrivial R] :
    (W.biX₂ - W.biX₁).orderTop = ((-2 : ℤ) : WithTop ℤ) := by
  refine le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero ?_) ?_
  · rw [W.coeff_biX₂_sub_biX₁_neg_two]; exact one_ne_zero
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro j hj
    exact W.coeff_biX₂_sub_biX₁_of_lt (by exact_mod_cast hj)

private lemma d_ne_zero [Nontrivial R] : (W.biX₂ - W.biX₁) ≠ 0 :=
  W.isUnit_biX₂_sub_biX₁.ne_zero

private lemma order_d [Nontrivial R] : (W.biX₂ - W.biX₁).order = -2 := by
  have : ((W.biX₂ - W.biX₁).order : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) := by
    rw [HahnSeries.order_eq_orderTop_of_ne_zero W.d_ne_zero, W.orderTop_d]
  exact_mod_cast this

private lemma leadingCoeff_d [Nontrivial R] : (W.biX₂ - W.biX₁).leadingCoeff = 1 := by
  rw [HahnSeries.leadingCoeff_eq, W.order_d, W.coeff_biX₂_sub_biX₁_neg_two]

private lemma orderTop_inv_d [Nontrivial R] :
    (Ring.inverse (W.biX₂ - W.biX₁)).orderTop = ((2 : ℤ) : WithTop ℤ) := by
  have hmul : (W.biX₂ - W.biX₁) * Ring.inverse (W.biX₂ - W.biX₁) = 1 :=
    Ring.mul_inverse_cancel _ W.isUnit_biX₂_sub_biX₁
  have hinv0 : Ring.inverse (W.biX₂ - W.biX₁) ≠ 0 := by
    obtain ⟨u, hu⟩ := W.isUnit_biX₂_sub_biX₁
    rw [← hu, Ring.inverse_unit]; exact u⁻¹.ne_zero
  have hlc : (W.biX₂ - W.biX₁).leadingCoeff *
      (Ring.inverse (W.biX₂ - W.biX₁)).leadingCoeff ≠ 0 := by
    rw [W.leadingCoeff_d, one_mul]; exact HahnSeries.leadingCoeff_ne_zero.mpr hinv0
  have h := HahnSeries.orderTop_mul_of_ne_zero hlc
  rw [hmul, HahnSeries.orderTop_one, W.orderTop_d] at h
  -- `h : 0 = ↑(-2) + orderTop (inv)`
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
    (HahnSeries.orderTop_ne_top.mpr hinv0)
  rw [← hk] at h ⊢
  rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at h
  rw [WithTop.coe_eq_coe]
  omega

/-! ### The principal part of the slope `λ` -/

/-- The principal part `Λ = z₂⁻¹·(-1) + z₂·(-x₁) + z₂²·(-y₁ - a₁x₁)` of the slope `λ`, matching
`λ` in `z₂`-degrees `< 3`. -/
private noncomputable def lambdaPrincipal (W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ :=
  HahnSeries.single (-1) (-1)
    + HahnSeries.single 1 (-W.formalX)
    + HahnSeries.single 2 (-W.formalY - HahnSeries.C W.a₁ * W.formalX)

/-- `Λ · y` coefficient, reduced to `single`-multiplications (no antidiagonal). -/
private lemma coeff_lambdaPrincipal_mul (y : (R⸨X⸩)⸨X⸩) (g : ℤ) :
    (W.lambdaPrincipal * y).coeff g
      = (-1) * y.coeff (g + 1)
        + (-W.formalX) * y.coeff (g - 1)
        + (-W.formalY - HahnSeries.C W.a₁ * W.formalX) * y.coeff (g - 2) := by
  rw [lambdaPrincipal, add_mul, add_mul, HahnSeries.coeff_add, HahnSeries.coeff_add,
    HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul,
    sub_neg_eq_add]

private lemma orderTop_n_sub_lambdaPrincipal_mul_d [Nontrivial R] :
    ((1 : ℤ) : WithTop ℤ) ≤
      ((W.biY₂ - W.biY₁) - W.lambdaPrincipal * (W.biX₂ - W.biX₁)).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  have hg1 : g < 1 := by exact_mod_cast hg
  rw [HahnSeries.coeff_sub, W.coeff_lambdaPrincipal_mul]
  rcases lt_or_ge g (-3 : ℤ) with hlt | hge
  · rw [W.coeff_n_of_lt hlt, W.coeff_biX₂_sub_biX₁_of_lt (show g + 1 < -2 by omega),
      W.coeff_biX₂_sub_biX₁_of_lt (show g - 1 < -2 by omega),
      W.coeff_biX₂_sub_biX₁_of_lt (show g - 2 < -2 by omega)]
    ring
  · have hz3 : (W.biX₂ - W.biX₁).coeff (-3) = 0 := W.coeff_biX₂_sub_biX₁_of_lt (by norm_num)
    have hz4 : (W.biX₂ - W.biX₁).coeff (-4) = 0 := W.coeff_biX₂_sub_biX₁_of_lt (by norm_num)
    have hz5 : (W.biX₂ - W.biX₁).coeff (-5) = 0 := W.coeff_biX₂_sub_biX₁_of_lt (by norm_num)
    interval_cases g <;>
      simp only [W.coeff_n_neg_three, W.coeff_n_neg_two, W.coeff_n_neg_one, W.coeff_n_zero,
        W.coeff_biX₂_sub_biX₁_neg_two, W.coeff_d_neg_one, W.coeff_d_zero, W.coeff_d_one,
        hz3, hz4, hz5, show (-3 : ℤ) + 1 = -2 by norm_num,
        show (-3 : ℤ) - 1 = -4 by norm_num, show (-3 : ℤ) - 2 = -5 by norm_num,
        show (-2 : ℤ) + 1 = -1 by norm_num, show (-2 : ℤ) - 1 = -3 by norm_num,
        show (-2 : ℤ) - 2 = -4 by norm_num, show (-1 : ℤ) + 1 = 0 by norm_num,
        show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) - 2 = -3 by norm_num,
        show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
        show (0 : ℤ) - 2 = -2 by norm_num] <;> ring

/-- The slope `λ` agrees with its principal part `Λ` in `z₂`-degrees `< 3`. -/
private lemma orderTop_lambda_sub_principal [Nontrivial R] :
    ((3 : ℤ) : WithTop ℤ) ≤ (W.formalLambda - W.lambdaPrincipal).orderTop := by
  have hmul : (W.biX₂ - W.biX₁) * Ring.inverse (W.biX₂ - W.biX₁) = 1 :=
    Ring.mul_inverse_cancel _ W.isUnit_biX₂_sub_biX₁
  have hfac : ((W.biY₂ - W.biY₁) - W.lambdaPrincipal * (W.biX₂ - W.biX₁))
      * Ring.inverse (W.biX₂ - W.biX₁) = W.formalLambda - W.lambdaPrincipal := by
    rw [formalLambda, sub_mul, mul_assoc, hmul, mul_one]
  calc ((3 : ℤ) : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) + ((2 : ℤ) : WithTop ℤ) := by
        rw [← WithTop.coe_add]; norm_num
    _ ≤ ((W.biY₂ - W.biY₁) - W.lambdaPrincipal * (W.biX₂ - W.biX₁)).orderTop
          + (Ring.inverse (W.biX₂ - W.biX₁)).orderTop :=
        add_le_add W.orderTop_n_sub_lambdaPrincipal_mul_d (le_of_eq W.orderTop_inv_d.symm)
    _ ≤ _ := by rw [← hfac]; exact HahnSeries.orderTop_add_le_mul

/-! ### Coefficients and orders of the principal-part powers -/

/-- `(C(Ca) * x).coeff g = Ca * x.coeff g` (the constant `C(Ca)` is a `single 0`). -/
private lemma coeff_CC_mul (a : R) (x : (R⸨X⸩)⸨X⸩) (g : ℤ) :
    (HahnSeries.C (HahnSeries.C a) * x).coeff g = HahnSeries.C a * x.coeff g := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero]

/-- `(C(Ca)).coeff 0 = Ca`. -/
private lemma coeff_CC_zero (a : R) :
    (HahnSeries.C (HahnSeries.C a) : (R⸨X⸩)⸨X⸩).coeff 0 = HahnSeries.C a := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]

/-- `(C(Ca)).coeff g = 0` for `g ≠ 0`. -/
private lemma coeff_CC_of_ne (a : R) {g : ℤ} (hg : g ≠ 0) :
    (HahnSeries.C (HahnSeries.C a) : (R⸨X⸩)⸨X⸩).coeff g = 0 := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg]

/-! Coefficients of the principal part `Λ` (support `{-1, 1, 2}`). -/

private lemma coeff_lamP_of_lt {g : ℤ} (hg : g < -1) : W.lambdaPrincipal.coeff g = 0 := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]
  ring

private lemma coeff_lamP_neg_one : W.lambdaPrincipal.coeff (-1) = -1 := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, ite_eq_left rfl, ite_eq_right (by norm_num),
    ite_eq_right (by norm_num)]
  ring

private lemma coeff_lamP_zero : W.lambdaPrincipal.coeff 0 = 0 := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, ite_eq_right (by norm_num), ite_eq_right (by norm_num),
    ite_eq_right (by norm_num)]
  ring

private lemma coeff_lamP_one : W.lambdaPrincipal.coeff 1 = -W.formalX := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, ite_eq_right (by norm_num), ite_eq_left rfl,
    ite_eq_right (by norm_num)]
  ring

private lemma coeff_lamP_two :
    W.lambdaPrincipal.coeff 2 = -W.formalY - HahnSeries.C W.a₁ * W.formalX := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, ite_eq_right (by norm_num), ite_eq_right (by norm_num),
    ite_eq_left rfl]
  ring

private lemma orderTop_lamP : ((-1 : ℤ) : WithTop ℤ) ≤ W.lambdaPrincipal.orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  exact W.coeff_lamP_of_lt (by exact_mod_cast hg)

private lemma orderTop_lamP_sq : ((-2 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal ^ 2).orderTop := by
  rw [sq]
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  rw [show ((-2 : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) by
    rw [← WithTop.coe_add]; norm_num]
  exact add_le_add W.orderTop_lamP W.orderTop_lamP

private lemma orderTop_lamP_cube : ((-3 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal ^ 3).orderTop := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal ^ 2 * W.lambdaPrincipal by ring]
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  rw [show ((-3 : ℤ) : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) by
    rw [← WithTop.coe_add]; norm_num]
  exact add_le_add W.orderTop_lamP_sq W.orderTop_lamP

private lemma coeff_lamP_sq_of_lt {g : ℤ} (hg : g < -2) : (W.lambdaPrincipal ^ 2).coeff g = 0 := by
  rw [sq, W.coeff_lambdaPrincipal_mul, W.coeff_lamP_of_lt (by omega), W.coeff_lamP_of_lt (by omega),
    W.coeff_lamP_of_lt (by omega)]
  ring

private lemma coeff_lamP_sq_neg_two : (W.lambdaPrincipal ^ 2).coeff (-2) = 1 := by
  rw [sq, W.coeff_lambdaPrincipal_mul, show (-2 : ℤ) + 1 = -1 by norm_num,
    show (-2 : ℤ) - 1 = -3 by norm_num, show (-2 : ℤ) - 2 = -4 by norm_num, W.coeff_lamP_neg_one,
    W.coeff_lamP_of_lt (by norm_num), W.coeff_lamP_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_sq_neg_one : (W.lambdaPrincipal ^ 2).coeff (-1) = 0 := by
  rw [sq, W.coeff_lambdaPrincipal_mul, show (-1 : ℤ) + 1 = 0 by norm_num,
    show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) - 2 = -3 by norm_num, W.coeff_lamP_zero,
    W.coeff_lamP_of_lt (by norm_num), W.coeff_lamP_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_sq_zero : (W.lambdaPrincipal ^ 2).coeff 0 = 2 * W.formalX := by
  rw [sq, W.coeff_lambdaPrincipal_mul, show (0 : ℤ) + 1 = 1 by norm_num,
    show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) - 2 = -2 by norm_num, W.coeff_lamP_one,
    W.coeff_lamP_neg_one, W.coeff_lamP_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_sq_one :
    (W.lambdaPrincipal ^ 2).coeff 1 = 2 * W.formalY + 2 * HahnSeries.C W.a₁ * W.formalX := by
  rw [sq, W.coeff_lambdaPrincipal_mul, show (1 : ℤ) + 1 = 2 by norm_num,
    show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) - 2 = -1 by norm_num, W.coeff_lamP_two,
    W.coeff_lamP_zero, W.coeff_lamP_neg_one]
  ring

private lemma coeff_lamP_cube_neg_three : (W.lambdaPrincipal ^ 3).coeff (-3) = -1 := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal * W.lambdaPrincipal ^ 2 by ring,
    W.coeff_lambdaPrincipal_mul, show (-3 : ℤ) + 1 = -2 by norm_num,
    show (-3 : ℤ) - 1 = -4 by norm_num, show (-3 : ℤ) - 2 = -5 by norm_num, W.coeff_lamP_sq_neg_two,
    W.coeff_lamP_sq_of_lt (by norm_num), W.coeff_lamP_sq_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_cube_neg_two : (W.lambdaPrincipal ^ 3).coeff (-2) = 0 := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal * W.lambdaPrincipal ^ 2 by ring,
    W.coeff_lambdaPrincipal_mul, show (-2 : ℤ) + 1 = -1 by norm_num,
    show (-2 : ℤ) - 1 = -3 by norm_num, show (-2 : ℤ) - 2 = -4 by norm_num, W.coeff_lamP_sq_neg_one,
    W.coeff_lamP_sq_of_lt (by norm_num), W.coeff_lamP_sq_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_cube_neg_one : (W.lambdaPrincipal ^ 3).coeff (-1) = -3 * W.formalX := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal * W.lambdaPrincipal ^ 2 by ring,
    W.coeff_lambdaPrincipal_mul, show (-1 : ℤ) + 1 = 0 by norm_num,
    show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) - 2 = -3 by norm_num, W.coeff_lamP_sq_zero,
    W.coeff_lamP_sq_neg_two, W.coeff_lamP_sq_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_cube_zero :
    (W.lambdaPrincipal ^ 3).coeff 0 = -3 * W.formalY - 3 * HahnSeries.C W.a₁ * W.formalX := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal * W.lambdaPrincipal ^ 2 by ring,
    W.coeff_lambdaPrincipal_mul, show (0 : ℤ) + 1 = 1 by norm_num,
    show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) - 2 = -2 by norm_num, W.coeff_lamP_sq_one,
    W.coeff_lamP_sq_neg_one, W.coeff_lamP_sq_neg_two]
  ring

private lemma coeff_biX₂_neg_two : W.biX₂.coeff (-2) = 1 := by
  rw [coeff_biX₂, coeff_formalX_neg_two, map_one]

private lemma coeff_biX₂_neg_one : W.biX₂.coeff (-1) = -HahnSeries.C W.a₁ := by
  rw [coeff_biX₂, coeff_formalX_neg_one, map_neg]

private lemma coeff_biX₂_zero : W.biX₂.coeff 0 = -HahnSeries.C W.a₂ := by
  rw [coeff_biX₂, coeff_formalX_zero, map_neg]

private lemma coeff_biX₂_one : W.biX₂.coeff 1 = -HahnSeries.C W.a₃ := by
  rw [coeff_biX₂, coeff_formalX_one, map_neg]

private lemma coeff_biX₂_of_lt {g : ℤ} (hg : g < -2) : W.biX₂.coeff g = 0 := by
  rw [coeff_biX₂, W.coeff_formalX_of_lt hg, map_zero]

/-- `(Λ * x₁).coeff g = Λ.coeff g * x(z₁)` (since `x₁` is `z₂`-constant). -/
private lemma coeff_lamP_mul_biX₁ (g : ℤ) :
    (W.lambdaPrincipal * W.biX₁).coeff g = W.lambdaPrincipal.coeff g * W.formalX := by
  rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_mul_single, sub_zero]

private lemma coeff_lamP_mul_biX₂_neg_three : (W.lambdaPrincipal * W.biX₂).coeff (-3) = -1 := by
  rw [W.coeff_lambdaPrincipal_mul, show (-3 : ℤ) + 1 = -2 by norm_num,
    show (-3 : ℤ) - 1 = -4 by norm_num, show (-3 : ℤ) - 2 = -5 by norm_num, W.coeff_biX₂_neg_two,
    W.coeff_biX₂_of_lt (by norm_num), W.coeff_biX₂_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_mul_biX₂_neg_two :
    (W.lambdaPrincipal * W.biX₂).coeff (-2) = HahnSeries.C W.a₁ := by
  rw [W.coeff_lambdaPrincipal_mul, show (-2 : ℤ) + 1 = -1 by norm_num,
    show (-2 : ℤ) - 1 = -3 by norm_num, show (-2 : ℤ) - 2 = -4 by norm_num, W.coeff_biX₂_neg_one,
    W.coeff_biX₂_of_lt (by norm_num), W.coeff_biX₂_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_mul_biX₂_neg_one :
    (W.lambdaPrincipal * W.biX₂).coeff (-1) = HahnSeries.C W.a₂ - W.formalX := by
  rw [W.coeff_lambdaPrincipal_mul, show (-1 : ℤ) + 1 = 0 by norm_num,
    show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) - 2 = -3 by norm_num, W.coeff_biX₂_zero,
    W.coeff_biX₂_neg_two, W.coeff_biX₂_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_mul_biX₂_zero :
    (W.lambdaPrincipal * W.biX₂).coeff 0 = HahnSeries.C W.a₃ - W.formalY := by
  rw [W.coeff_lambdaPrincipal_mul, show (0 : ℤ) + 1 = 1 by norm_num,
    show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) - 2 = -2 by norm_num, W.coeff_biX₂_one,
    W.coeff_biX₂_neg_one, W.coeff_biX₂_neg_two]
  ring

private lemma orderTop_biX₂ : ((-2 : ℤ) : WithTop ℤ) ≤ W.biX₂.orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  rw [coeff_biX₂, W.coeff_formalX_of_lt (show g < -2 by exact_mod_cast hg), map_zero]

private lemma orderTop_biX₁ : ((0 : ℤ) : WithTop ℤ) ≤ W.biX₁.orderTop := by
  rw [biX₁, cConstRingHom, HahnSeries.C_apply]; exact HahnSeries.orderTop_single_le

private lemma orderTop_biY₁ : ((0 : ℤ) : WithTop ℤ) ≤ W.biY₁.orderTop := by
  rw [biY₁, cConstRingHom, HahnSeries.C_apply]; exact HahnSeries.orderTop_single_le

private lemma orderTop_CC (a : R) :
    ((0 : ℤ) : WithTop ℤ) ≤ (HahnSeries.C (HahnSeries.C a) : (R⸨X⸩)⸨X⸩).orderTop := by
  rw [HahnSeries.C_apply]; exact HahnSeries.orderTop_single_le

/-- `orderTop (C(Ca) * x) ≥ orderTop x`. -/
private lemma le_orderTop_CC_mul (a : R) (x : (R⸨X⸩)⸨X⸩) :
    x.orderTop ≤ (HahnSeries.C (HahnSeries.C a) * x).orderTop := by
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  simpa using add_le_add (orderTop_CC a) (le_refl x.orderTop)

/-- `orderTop (Λ * y) ≥ -1 + orderTop y`. -/
private lemma le_orderTop_lamP_mul (y : (R⸨X⸩)⸨X⸩) :
    ((-1 : ℤ) : WithTop ℤ) + y.orderTop ≤ (W.lambdaPrincipal * y).orderTop :=
  le_trans (add_le_add W.orderTop_lamP (le_refl y.orderTop)) HahnSeries.orderTop_add_le_mul

private lemma le_orderTop_add' {a b : (R⸨X⸩)⸨X⸩} {c : WithTop ℤ}
    (ha : c ≤ a.orderTop) (hb : c ≤ b.orderTop) : c ≤ (a + b).orderTop :=
  le_trans (le_min ha hb) HahnSeries.min_orderTop_le_orderTop_add

private lemma le_orderTop_sub' {a b : (R⸨X⸩)⸨X⸩} {c : WithTop ℤ}
    (ha : c ≤ a.orderTop) (hb : c ≤ b.orderTop) : c ≤ (a - b).orderTop := by
  rw [sub_eq_add_neg]
  exact le_orderTop_add' ha (by rwa [HahnSeries.orderTop_neg])

/-! ### The `Λ`-only part `Zpure` and the `h`-cofactor `Q` of `y₃ - biY₁` -/

/-- The `Λ`-only part of `y₃ - y(z₁)` (the Vieta expansion with `λ` replaced by its principal part
`Λ`). Written without numeric multipliers to ease the order bookkeeping. -/
private noncomputable def zpureY (W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ :=
  -W.lambdaPrincipal ^ 3
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal ^ 2
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal ^ 2
    + HahnSeries.C (HahnSeries.C W.a₂) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * (HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal)
    + W.lambdaPrincipal * W.biX₁ + W.lambdaPrincipal * W.biX₁ + W.lambdaPrincipal * W.biX₂
    + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₁ + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂
    + HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.C (HahnSeries.C W.a₂)
    - W.biY₁ - W.biY₁ - HahnSeries.C (HahnSeries.C W.a₃)

/-- The cofactor `Q` with `y₃ - y(z₁) = Zpure + (λ - Λ)·Q`. -/
private noncomputable def qY (W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ :=
  -W.lambdaPrincipal ^ 2 - W.lambdaPrincipal ^ 2 - W.lambdaPrincipal ^ 2
    - W.lambdaPrincipal * (W.formalLambda - W.lambdaPrincipal)
    - W.lambdaPrincipal * (W.formalLambda - W.lambdaPrincipal)
    - W.lambdaPrincipal * (W.formalLambda - W.lambdaPrincipal)
    - (W.formalLambda - W.lambdaPrincipal) * (W.formalLambda - W.lambdaPrincipal)
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * (W.formalLambda - W.lambdaPrincipal)
    - HahnSeries.C (HahnSeries.C W.a₁) * (W.formalLambda - W.lambdaPrincipal)
    + HahnSeries.C (HahnSeries.C W.a₂)
    - HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.C (HahnSeries.C W.a₁)
    + W.biX₁ + W.biX₁ + W.biX₂

private lemma formalYThree_sub_biY₁_eq :
    W.formalYThree - W.biY₁
      = W.zpureY + (W.formalLambda - W.lambdaPrincipal) * W.qY := by
  unfold formalYThree formalXThree formalNu zpureY qY
  ring

/-- Each summand of `Zpure` has `z₂`-order `≥ -3`, hence so does `Zpure`. -/
private lemma orderTop_zpureY_ge [Nontrivial R] :
    ((-3 : ℤ) : WithTop ℤ) ≤ W.zpureY.orderTop := by
  have hCCL2 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal ^ 2).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ -2))
      (le_trans W.orderTop_lamP_sq (le_orderTop_CC_mul _ _))
  have hCC2L : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₂) * W.lambdaPrincipal).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ -1))
      (le_trans W.orderTop_lamP (le_orderTop_CC_mul _ _))
  have hCC1CC1L : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) *
          (HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal)).orderTop :=
    le_trans (le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ -1))
      (le_trans W.orderTop_lamP (le_orderTop_CC_mul _ _))) (le_orderTop_CC_mul _ _)
  have hLbiX1 : ((-3 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal * W.biX₁).orderTop := by
    refine le_trans ?_ (W.le_orderTop_lamP_mul W.biX₁)
    rw [show ((-3 : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add (le_refl _)
      (le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)) W.orderTop_biX₁)
  have hLbiX2 : ((-3 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal * W.biX₂).orderTop := by
    refine le_trans ?_ (W.le_orderTop_lamP_mul W.biX₂)
    rw [show ((-3 : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add (le_refl _) W.orderTop_biX₂
  have hCC1biX1 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * W.biX₁).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ 0))
      (le_trans W.orderTop_biX₁ (le_orderTop_CC_mul _ _))
  have hCC1biX2 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ -2))
      (le_trans W.orderTop_biX₂ (le_orderTop_CC_mul _ _))
  have hCC1CC2 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.C (HahnSeries.C W.a₂)
          : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ 0))
      (le_trans (orderTop_CC _) (le_orderTop_CC_mul _ _))
  have hbiY1 : ((-3 : ℤ) : WithTop ℤ) ≤ W.biY₁.orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ 0)) W.orderTop_biY₁
  have hCC3 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₃) : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ 0)) (orderTop_CC _)
  have hL3 : ((-3 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal ^ 3).orderTop := W.orderTop_lamP_cube
  unfold zpureY
  refine le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_add' (le_orderTop_add'
    (le_orderTop_add' (le_orderTop_add' (le_orderTop_add' (le_orderTop_add' (le_orderTop_sub'
    (le_orderTop_add' (le_orderTop_sub' (le_orderTop_sub' ?_ hCCL2) hCCL2) hCC2L) hCC1CC1L)
    hLbiX1) hLbiX1) hLbiX2) hCC1biX1) hCC1biX2) hCC1CC2) hbiY1) hbiY1) hCC3
  rw [HahnSeries.orderTop_neg]; exact hL3

/-- Each summand of `Q` has `z₂`-order `≥ -2`, hence so does `Q`. -/
private lemma orderTop_qY_ge [Nontrivial R] : ((-2 : ℤ) : WithTop ℤ) ≤ W.qY.orderTop := by
  have hh : ((3 : ℤ) : WithTop ℤ) ≤ (W.formalLambda - W.lambdaPrincipal).orderTop :=
    W.orderTop_lambda_sub_principal
  have hL2 : ((-2 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal ^ 2).orderTop := W.orderTop_lamP_sq
  have hLh : ((-2 : ℤ) : WithTop ℤ)
      ≤ (W.lambdaPrincipal * (W.formalLambda - W.lambdaPrincipal)).orderTop := by
    refine le_trans ?_ (W.le_orderTop_lamP_mul _)
    exact le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ -1 + 3))
      (add_le_add (le_refl _) hh)
  have hhh : ((-2 : ℤ) : WithTop ℤ)
      ≤ ((W.formalLambda - W.lambdaPrincipal) * (W.formalLambda - W.lambdaPrincipal)).orderTop := by
    refine le_trans ?_ HahnSeries.orderTop_add_le_mul
    exact le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 3 + 3)) (add_le_add hh hh)
  have hCCL : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ -1))
      (le_trans W.orderTop_lamP (le_orderTop_CC_mul _ _))
  have hCCh : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * (W.formalLambda - W.lambdaPrincipal)).orderTop :=
    le_trans (le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 3)) hh)
      (le_orderTop_CC_mul _ _)
  have hCC2 : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₂) : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)) (orderTop_CC _)
  have hCC1CC1 : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.C (HahnSeries.C W.a₁)
          : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0))
      (le_trans (orderTop_CC _) (le_orderTop_CC_mul _ _))
  have hbiX1 : ((-2 : ℤ) : WithTop ℤ) ≤ W.biX₁.orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)) W.orderTop_biX₁
  have hbiX2 : ((-2 : ℤ) : WithTop ℤ) ≤ W.biX₂.orderTop := W.orderTop_biX₂
  unfold qY
  refine le_orderTop_add' (le_orderTop_add' (le_orderTop_add' (le_orderTop_sub' (le_orderTop_add'
    (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub'
    (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub'
    (le_orderTop_sub' (le_orderTop_sub' ?_ hL2) hL2) hLh) hLh) hLh) hhh) hCCL) hCCL) hCCL) hCCL)
    hCCh) hCCh) hCC2) hCC1CC1) hbiX1) hbiX1) hbiX2
  rw [HahnSeries.orderTop_neg]; exact hL2

/-- `Zpure.coeff g = 0` for `g < 1` (its low coefficients cancel; `Silverman AEC IV.1`). -/
private lemma coeff_zpureY_of_lt [Nontrivial R] {g : ℤ} (hg : g < 1) : W.zpureY.coeff g = 0 := by
  rcases lt_or_ge g (-3) with hlt | hge
  · exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (by exact_mod_cast hlt) W.orderTop_zpureY_ge)
  · have hg1 : g ≤ 0 := by omega
    unfold zpureY
    interval_cases g <;>
      simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, HahnSeries.coeff_neg, coeff_CC_mul,
        W.coeff_lamP_sq_of_lt (show (-3 : ℤ) < -2 by norm_num),
        W.coeff_lamP_of_lt (show (-3 : ℤ) < -1 by norm_num),
        W.coeff_lamP_of_lt (show (-2 : ℤ) < -1 by norm_num),
        W.coeff_biX₂_of_lt (show (-3 : ℤ) < -2 by norm_num),
        W.coeff_biX₁_of_ne (show (-3 : ℤ) ≠ 0 by norm_num),
        W.coeff_biX₁_of_ne (show (-2 : ℤ) ≠ 0 by norm_num),
        W.coeff_biX₁_of_ne (show (-1 : ℤ) ≠ 0 by norm_num),
        W.coeff_biY₁_of_ne (show (-3 : ℤ) ≠ 0 by norm_num),
        W.coeff_biY₁_of_ne (show (-2 : ℤ) ≠ 0 by norm_num),
        W.coeff_biY₁_of_ne (show (-1 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₂ (show (-3 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₂ (show (-2 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₂ (show (-1 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₃ (show (-3 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₃ (show (-2 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₃ (show (-1 : ℤ) ≠ 0 by norm_num),
        W.coeff_lamP_mul_biX₁, W.coeff_lamP_cube_neg_three, W.coeff_lamP_cube_neg_two,
        W.coeff_lamP_cube_neg_one, W.coeff_lamP_cube_zero, W.coeff_lamP_sq_neg_two,
        W.coeff_lamP_sq_neg_one, W.coeff_lamP_sq_zero, W.coeff_lamP_neg_one, W.coeff_lamP_zero,
        W.coeff_lamP_mul_biX₂_neg_three, W.coeff_lamP_mul_biX₂_neg_two,
        W.coeff_lamP_mul_biX₂_neg_one, W.coeff_lamP_mul_biX₂_zero, W.coeff_biX₁_zero,
        W.coeff_biX₂_neg_two, W.coeff_biX₂_neg_one, W.coeff_biX₂_zero, W.coeff_biY₁_zero,
        coeff_CC_zero] <;> ring

/-! ### `y₃` is a unit -/

private lemma orderTop_formalYThree_sub_biY₁ [Nontrivial R] :
    ((1 : ℤ) : WithTop ℤ) ≤ (W.formalYThree - W.biY₁).orderTop := by
  rw [W.formalYThree_sub_biY₁_eq]
  refine le_orderTop_add' ?_ ?_
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro g hg
    exact W.coeff_zpureY_of_lt (by exact_mod_cast hg)
  · refine le_trans ?_ HahnSeries.orderTop_add_le_mul
    rw [show ((1 : ℤ) : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add W.orderTop_lambda_sub_principal W.orderTop_qY_ge

/-- **The analytic core of the Weierstrass formal group law.** The third `y`-coordinate `y₃` is a
unit of `R⸨z₁⸩⸨z₂⸩`. Its `z₂`-order is `0` with leading coefficient the unit `y(z₁) = W.formalY`,
which makes the formal group series `F_E := -x₃·y₃⁻¹` well-defined. (Silverman AEC IV.1.) -/
theorem isUnit_formalYThree : IsUnit W.formalYThree := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton _
  · have hbiord : W.biY₁.orderTop = ((0 : ℤ) : WithTop ℤ) := by
      rw [biY₁, cConstRingHom, HahnSeries.C_apply,
        HahnSeries.orderTop_single W.isUnit_formalY.ne_zero]
    have hlt : W.biY₁.orderTop < (W.formalYThree - W.biY₁).orderTop := by
      rw [hbiord]
      exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (0 : ℤ) < 1))
        W.orderTop_formalYThree_sub_biY₁
    refine HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ (AddGroup.isAddUnit _)
    have hlc : W.formalYThree.leadingCoeff = W.formalY := by
      rw [show W.formalYThree = W.biY₁ + (W.formalYThree - W.biY₁) by ring,
        HahnSeries.leadingCoeff_add_eq_left hlt, biY₁, cConstRingHom, HahnSeries.C_apply,
        HahnSeries.leadingCoeff_of_single]
    rw [hlc]
    exact W.isUnit_formalY

/-- The `z₂`-order of `y₃` is `0` (its leading coefficient sits in `z₂`-degree `0`). -/
theorem orderTop_formalYThree [Nontrivial R] :
    W.formalYThree.orderTop = (0 : WithTop ℤ) := by
  have hbiord : W.biY₁.orderTop = ((0 : ℤ) : WithTop ℤ) := by
    rw [biY₁, cConstRingHom, HahnSeries.C_apply,
      HahnSeries.orderTop_single W.isUnit_formalY.ne_zero]
  have hlt : W.biY₁.orderTop < (W.formalYThree - W.biY₁).orderTop := by
    rw [hbiord]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (0 : ℤ) < 1))
      W.orderTop_formalYThree_sub_biY₁
  rw [show W.formalYThree = W.biY₁ + (W.formalYThree - W.biY₁) by ring,
    HahnSeries.orderTop_add_eq_left hlt, hbiord, WithTop.coe_zero]

/-- The leading `z₂`-coefficient of `y₃` is the unit `y(z₁) = W.formalY`. -/
theorem leadingCoeff_formalYThree [Nontrivial R] :
    W.formalYThree.leadingCoeff = W.formalY := by
  have hbiord : W.biY₁.orderTop = ((0 : ℤ) : WithTop ℤ) := by
    rw [biY₁, cConstRingHom, HahnSeries.C_apply,
      HahnSeries.orderTop_single W.isUnit_formalY.ne_zero]
  have hlt : W.biY₁.orderTop < (W.formalYThree - W.biY₁).orderTop := by
    rw [hbiord]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (0 : ℤ) < 1))
      W.orderTop_formalYThree_sub_biY₁
  rw [show W.formalYThree = W.biY₁ + (W.formalYThree - W.biY₁) by ring,
    HahnSeries.leadingCoeff_add_eq_left hlt, biY₁, cConstRingHom, HahnSeries.C_apply,
    HahnSeries.leadingCoeff_of_single]

/-! ### `x₃` is a unit of `z₂`-order `0`

The `z₂⁻²` poles of `λ²` and `x₂` cancel in `x₃ = λ² + a₁λ - a₂ - x₁ - x₂`, leaving a series of
`z₂`-order `0` with leading coefficient the unit `x(z₁) = W.formalX`. The argument mirrors the `y₃`
computation: peel off the principal part `Λ` of `λ` and bound the higher-order corrections. -/

/-- `x(z₁) = W.formalX` is nonzero over a nontrivial ring (`x` has a `z₁⁻²` pole). -/
private lemma formalX_ne_zero [Nontrivial R] : W.formalX ≠ 0 := fun h => by
  simpa [h] using W.coeff_formalX_neg_two

private lemma orderTop_biX₁_eq [Nontrivial R] : W.biX₁.orderTop = ((0 : ℤ) : WithTop ℤ) := by
  rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.orderTop_single W.formalX_ne_zero]

/-- The `Λ`-only part of `x₃ - x(z₁)` (the Vieta expansion with `λ` replaced by its principal part
`Λ`). Its low `z₂`-coefficients cancel. -/
private noncomputable def zpureX (W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ :=
  W.lambdaPrincipal ^ 2 + HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₂) - W.biX₁ - W.biX₂ - W.biX₁

/-- The cofactor `Q` with `x₃ - x(z₁) = Zpure + (λ - Λ)·Q`, i.e. `Q = 2Λ + (λ - Λ) + a₁`. -/
private noncomputable def qX (W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ :=
  W.lambdaPrincipal + W.lambdaPrincipal + (W.formalLambda - W.lambdaPrincipal)
    + HahnSeries.C (HahnSeries.C W.a₁)

private lemma formalXThree_sub_biX₁_eq :
    W.formalXThree - W.biX₁ = W.zpureX + (W.formalLambda - W.lambdaPrincipal) * W.qX := by
  unfold formalXThree zpureX qX
  ring

/-- Each summand of `Zpure` (for `x₃`) has `z₂`-order `≥ -2`, hence so does `Zpure`. -/
private lemma orderTop_zpureX_ge [Nontrivial R] :
    ((-2 : ℤ) : WithTop ℤ) ≤ W.zpureX.orderTop := by
  have hL2 : ((-2 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal ^ 2).orderTop := W.orderTop_lamP_sq
  have hCCL : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ -1))
      (le_trans W.orderTop_lamP (le_orderTop_CC_mul _ _))
  have hCC2 : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₂) : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)) (orderTop_CC _)
  have hbiX1 : ((-2 : ℤ) : WithTop ℤ) ≤ W.biX₁.orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)) W.orderTop_biX₁
  have hbiX2 : ((-2 : ℤ) : WithTop ℤ) ≤ W.biX₂.orderTop := W.orderTop_biX₂
  unfold zpureX
  exact le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub'
    (le_orderTop_add' hL2 hCCL) hCC2) hbiX1) hbiX2) hbiX1

/-- `Zpure.coeff g = 0` for `g < 1` (its low coefficients cancel; Silverman AEC IV.1). -/
private lemma coeff_zpureX_of_lt [Nontrivial R] {g : ℤ} (hg : g < 1) : W.zpureX.coeff g = 0 := by
  rcases lt_or_ge g (-2) with hlt | hge
  · exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (by exact_mod_cast hlt) W.orderTop_zpureX_ge)
  · have hg0 : g ≤ 0 := by omega
    unfold zpureX
    interval_cases g <;>
      simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, coeff_CC_mul,
        W.coeff_lamP_sq_neg_two, W.coeff_lamP_sq_neg_one, W.coeff_lamP_sq_zero,
        W.coeff_lamP_of_lt (show (-2 : ℤ) < -1 by norm_num), W.coeff_lamP_neg_one,
        W.coeff_lamP_zero,
        coeff_CC_of_ne W.a₂ (show (-2 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₂ (show (-1 : ℤ) ≠ 0 by norm_num), coeff_CC_zero W.a₂,
        W.coeff_biX₁_of_ne (show (-2 : ℤ) ≠ 0 by norm_num),
        W.coeff_biX₁_of_ne (show (-1 : ℤ) ≠ 0 by norm_num), W.coeff_biX₁_zero,
        W.coeff_biX₂_neg_two, W.coeff_biX₂_neg_one, W.coeff_biX₂_zero] <;> ring

/-- Each summand of `Q` (for `x₃`) has `z₂`-order `≥ -1`, hence so does `Q`. -/
private lemma orderTop_qX_ge [Nontrivial R] : ((-1 : ℤ) : WithTop ℤ) ≤ W.qX.orderTop := by
  have hL : ((-1 : ℤ) : WithTop ℤ) ≤ W.lambdaPrincipal.orderTop := W.orderTop_lamP
  have hh : ((-1 : ℤ) : WithTop ℤ) ≤ (W.formalLambda - W.lambdaPrincipal).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 3)) W.orderTop_lambda_sub_principal
  have hCC1 : ((-1 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0)) (orderTop_CC _)
  unfold qX
  exact le_orderTop_add' (le_orderTop_add' (le_orderTop_add' hL hL) hh) hCC1

private lemma orderTop_formalXThree_sub_biX₁ [Nontrivial R] :
    ((1 : ℤ) : WithTop ℤ) ≤ (W.formalXThree - W.biX₁).orderTop := by
  rw [W.formalXThree_sub_biX₁_eq]
  refine le_orderTop_add' ?_ ?_
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro g hg
    exact W.coeff_zpureX_of_lt (by exact_mod_cast hg)
  · refine le_trans ?_ HahnSeries.orderTop_add_le_mul
    rw [show ((1 : ℤ) : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add W.orderTop_lambda_sub_principal
      (le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ -1)) W.orderTop_qX_ge)

/-- The `z₂`-order of `x₃` is `0`. -/
theorem orderTop_formalXThree [Nontrivial R] :
    W.formalXThree.orderTop = (0 : WithTop ℤ) := by
  have hlt : W.biX₁.orderTop < (W.formalXThree - W.biX₁).orderTop := by
    rw [W.orderTop_biX₁_eq]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (0 : ℤ) < 1))
      W.orderTop_formalXThree_sub_biX₁
  rw [show W.formalXThree = W.biX₁ + (W.formalXThree - W.biX₁) by ring,
    HahnSeries.orderTop_add_eq_left hlt, W.orderTop_biX₁_eq, WithTop.coe_zero]

/-- The leading `z₂`-coefficient of `x₃` is the unit `x(z₁) = W.formalX`. -/
theorem leadingCoeff_formalXThree [Nontrivial R] :
    W.formalXThree.leadingCoeff = W.formalX := by
  have hlt : W.biX₁.orderTop < (W.formalXThree - W.biX₁).orderTop := by
    rw [W.orderTop_biX₁_eq]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (0 : ℤ) < 1))
      W.orderTop_formalXThree_sub_biX₁
  rw [show W.formalXThree = W.biX₁ + (W.formalXThree - W.biX₁) by ring,
    HahnSeries.leadingCoeff_add_eq_left hlt, biX₁, cConstRingHom, HahnSeries.C_apply,
    HahnSeries.leadingCoeff_of_single]

/-! ### `z₂`-linear slices `x₃.coeff 1`, `x₃.coeff 2`, `y₃.coeff 1`

These `z₂`-slices (elements of `R⸨z₁⸩`) and their leading inner `z₁`-coefficients feed the
`z₂`-linear normalisation coefficient `coeff (single 1 1) = 1` of the Weierstrass formal group law
(issue #285, Silverman AEC IV.1). All computations use the principal-part `Λ = lambdaPrincipal`. -/

/-- `λ` agrees with its principal part `Λ` in `z₂`-degrees `< 3` (as `λ - Λ` has order `≥ 3`). -/
private lemma coeff_lambda_eq_principal [Nontrivial R] {g : ℤ} (hg : g < 3) :
    W.formalLambda.coeff g = W.lambdaPrincipal.coeff g := by
  have h : (W.formalLambda - W.lambdaPrincipal).coeff g = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (by exact_mod_cast hg) W.orderTop_lambda_sub_principal)
  rwa [HahnSeries.coeff_sub, sub_eq_zero] at h

private lemma coeff_lamP_three : W.lambdaPrincipal.coeff 3 = 0 := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, ite_eq_right (by norm_num), ite_eq_right (by norm_num),
    ite_eq_right (by norm_num)]
  ring

private lemma coeff_lamP_sq_two : (W.lambdaPrincipal ^ 2).coeff 2 = W.formalX ^ 2 := by
  rw [sq, W.coeff_lambdaPrincipal_mul, show (2 : ℤ) + 1 = 3 by norm_num,
    show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 2 = 0 by norm_num, W.coeff_lamP_three,
    W.coeff_lamP_one, W.coeff_lamP_zero]
  ring

/-! Order and squared leading coefficient of `x(z₁) = W.formalX`. -/

private lemma orderTop_formalX [Nontrivial R] :
    W.formalX.orderTop = ((-2 : ℤ) : WithTop ℤ) := by
  refine le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero ?_) ?_
  · rw [W.coeff_formalX_neg_two]; exact one_ne_zero
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro j hj
    exact W.coeff_formalX_of_lt (by exact_mod_cast hj)

private lemma order_formalX [Nontrivial R] : W.formalX.order = -2 := by
  have h : (W.formalX.order : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) := by
    rw [HahnSeries.order_eq_orderTop_of_ne_zero W.formalX_ne_zero, W.orderTop_formalX]
  exact_mod_cast h

private lemma coeff_formalX_sq_neg_four [Nontrivial R] : (W.formalX ^ 2).coeff (-4) = 1 := by
  have hlc : W.formalX.leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq, W.order_formalX, W.coeff_formalX_neg_two]
  have h := HahnSeries.coeff_mul_order_add_order W.formalX W.formalX
  rw [W.order_formalX, hlc, mul_one, show (-2 : ℤ) + (-2) = -4 by norm_num, ← sq] at h
  exact h

private lemma coeff_formalX_sq_of_lt [Nontrivial R] {g : ℤ} (hg : g < -4) :
    (W.formalX ^ 2).coeff g = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  refine lt_of_lt_of_le
    (show ((g : ℤ) : WithTop ℤ) < ((-4 : ℤ) : WithTop ℤ) by exact_mod_cast hg) ?_
  rw [sq]
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  rw [show ((-4 : ℤ) : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) by
    rw [← WithTop.coe_add]; norm_num]
  exact add_le_add (le_of_eq W.orderTop_formalX.symm) (le_of_eq W.orderTop_formalX.symm)

/-! ### The slice `x₃.coeff 1 = 2·y(z₁) + a₁·x(z₁) + a₃` -/

private lemma orderTop_lam_sub_prin_mul_qX [Nontrivial R] :
    ((2 : ℤ) : WithTop ℤ) ≤ ((W.formalLambda - W.lambdaPrincipal) * W.qX).orderTop := by
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  rw [show ((2 : ℤ) : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) by
    rw [← WithTop.coe_add]; norm_num]
  exact add_le_add W.orderTop_lambda_sub_principal W.orderTop_qX_ge

/-- The `z₂`-degree-`1` slice of `x₃` in `R⸨z₁⸩`: `x₃.coeff 1 = 2·y(z₁) + a₁·x(z₁) + a₃`. -/
theorem coeff_formalXThree_one [Nontrivial R] :
    W.formalXThree.coeff 1
      = W.formalY + W.formalY + HahnSeries.C W.a₁ * W.formalX + HahnSeries.C W.a₃ := by
  have hdecomp : W.formalXThree
      = W.biX₁ + W.zpureX + (W.formalLambda - W.lambdaPrincipal) * W.qX := by
    linear_combination W.formalXThree_sub_biX₁_eq
  rw [hdecomp, HahnSeries.coeff_add, HahnSeries.coeff_add,
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (show ((1 : ℤ) : WithTop ℤ) < ((2 : ℤ) : WithTop ℤ) by
        exact_mod_cast (by norm_num : (1 : ℤ) < 2)) W.orderTop_lam_sub_prin_mul_qX),
    W.coeff_biX₁_of_ne (show (1 : ℤ) ≠ 0 by norm_num), add_zero, zero_add, zpureX]
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, coeff_CC_mul, W.coeff_lamP_sq_one,
    W.coeff_lamP_one, coeff_CC_of_ne W.a₂ (show (1 : ℤ) ≠ 0 by norm_num),
    W.coeff_biX₁_of_ne (show (1 : ℤ) ≠ 0 by norm_num), W.coeff_biX₂_one]
  ring

theorem coeff_formalXThree_one_inner_neg_three [Nontrivial R] :
    (W.formalXThree.coeff 1).coeff (-3) = -2 := by
  rw [W.coeff_formalXThree_one]
  simp only [HahnSeries.coeff_add, HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero,
    W.coeff_formalY_neg_three, W.coeff_formalX_of_lt (show (-3 : ℤ) < -2 by norm_num),
    HahnSeries.coeff_single_of_ne (show (-3 : ℤ) ≠ 0 by norm_num)]
  ring

theorem coeff_formalXThree_one_inner_of_lt [Nontrivial R] {g : ℤ} (hg : g < -3) :
    (W.formalXThree.coeff 1).coeff g = 0 := by
  rw [W.coeff_formalXThree_one]
  simp only [HahnSeries.coeff_add, HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero,
    W.coeff_formalY_of_lt hg, W.coeff_formalX_of_lt (show g < -2 by omega),
    HahnSeries.coeff_single_of_ne (show g ≠ 0 by omega)]
  ring

/-! ### The slope coefficient `λ.coeff 3` and its leading inner behaviour -/

private lemma lam_sub_prin_mul_d :
    (W.formalLambda - W.lambdaPrincipal) * (W.biX₂ - W.biX₁)
      = (W.biY₂ - W.biY₁) - W.lambdaPrincipal * (W.biX₂ - W.biX₁) := by
  rw [sub_mul, W.formalLambda_mul_biX_sub]

private lemma orderTop_d_sub_single [Nontrivial R] :
    ((-1 : ℤ) : WithTop ℤ)
      ≤ ((W.biX₂ - W.biX₁) - HahnSeries.single (-2) 1).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  have hg2 : g < -1 := by exact_mod_cast hg
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single]
  by_cases hgeq : g = -2
  · rw [hgeq, W.coeff_biX₂_sub_biX₁_neg_two, ite_eq_left rfl, sub_self]
  · rw [W.coeff_biX₂_sub_biX₁_of_lt (by omega), ite_eq_right hgeq, sub_zero]

private lemma coeff_lam_sub_prin_mul_d_one [Nontrivial R] :
    ((W.formalLambda - W.lambdaPrincipal) * (W.biX₂ - W.biX₁)).coeff 1
      = (W.formalLambda - W.lambdaPrincipal).coeff 3 := by
  set h := W.formalLambda - W.lambdaPrincipal with hh
  have hvanish :
      (h * ((W.biX₂ - W.biX₁) - HahnSeries.single (-2) 1)).coeff 1 = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    refine lt_of_lt_of_le (show ((1 : ℤ) : WithTop ℤ) < ((2 : ℤ) : WithTop ℤ) by
      exact_mod_cast (by norm_num : (1 : ℤ) < 2)) ?_
    refine le_trans ?_ HahnSeries.orderTop_add_le_mul
    rw [show ((2 : ℤ) : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add W.orderTop_lambda_sub_principal W.orderTop_d_sub_single
  have hsplit : W.biX₂ - W.biX₁
      = HahnSeries.single (-2) 1 + ((W.biX₂ - W.biX₁) - HahnSeries.single (-2) 1) := by ring
  rw [hsplit, mul_add, HahnSeries.coeff_add, hvanish, add_zero, HahnSeries.coeff_mul_single,
    show (1 : ℤ) - (-2) = 3 by norm_num, mul_one]

private lemma coeff_lamP_mul_d_one :
    (W.lambdaPrincipal * (W.biX₂ - W.biX₁)).coeff 1
      = -(W.biX₂ - W.biX₁).coeff 2 - W.formalX * (W.biX₂ - W.biX₁).coeff 0
        + (-W.formalY - HahnSeries.C W.a₁ * W.formalX) * (W.biX₂ - W.biX₁).coeff (-1) := by
  rw [W.coeff_lambdaPrincipal_mul, show (1 : ℤ) + 1 = 2 by norm_num,
    show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) - 2 = -1 by norm_num]
  ring

/-- Closed form for the slope coefficient `(λ - Λ).coeff 3 ∈ R⸨z₁⸩`. -/
private lemma coeff_lam_sub_prin_three_eq [Nontrivial R] :
    (W.formalLambda - W.lambdaPrincipal).coeff 3
      = HahnSeries.C (W.formalY.coeff 1) + HahnSeries.C (W.formalX.coeff 2)
        - HahnSeries.C W.a₂ * W.formalX - W.formalX ^ 2
        - HahnSeries.C W.a₁ * W.formalY
        - HahnSeries.C W.a₁ * (HahnSeries.C W.a₁ * W.formalX) := by
  rw [← W.coeff_lam_sub_prin_mul_d_one, W.lam_sub_prin_mul_d, HahnSeries.coeff_sub,
    W.coeff_lamP_mul_d_one, HahnSeries.coeff_sub, W.coeff_biY₂,
    W.coeff_biY₁_of_ne (show (1 : ℤ) ≠ 0 by norm_num), sub_zero,
    show (W.biX₂ - W.biX₁).coeff 2 = HahnSeries.C (W.formalX.coeff 2) by
      rw [HahnSeries.coeff_sub, W.coeff_biX₂, W.coeff_biX₁_of_ne (show (2 : ℤ) ≠ 0 by norm_num),
        sub_zero],
    W.coeff_d_zero, W.coeff_d_neg_one]
  ring

private lemma coeff_lam_sub_prin_three_inner [Nontrivial R] :
    ((W.formalLambda - W.lambdaPrincipal).coeff 3).coeff (-4) = -1 := by
  rw [W.coeff_lam_sub_prin_three_eq]
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, sub_zero, W.coeff_formalX_sq_neg_four,
    W.coeff_formalX_of_lt (show (-4 : ℤ) < -2 by norm_num),
    W.coeff_formalY_of_lt (show (-4 : ℤ) < -3 by norm_num),
    HahnSeries.coeff_single_of_ne (show (-4 : ℤ) ≠ 0 by norm_num)]
  ring

private lemma coeff_lam_sub_prin_three_inner_of_lt [Nontrivial R] {g : ℤ} (hg : g < -4) :
    ((W.formalLambda - W.lambdaPrincipal).coeff 3).coeff g = 0 := by
  rw [W.coeff_lam_sub_prin_three_eq]
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, sub_zero, W.coeff_formalX_sq_of_lt hg,
    W.coeff_formalX_of_lt (show g < -2 by omega), W.coeff_formalY_of_lt (show g < -3 by omega),
    HahnSeries.coeff_single_of_ne (show g ≠ 0 by omega)]
  ring

/-! ### The slice `x₃.coeff 2` and its leading inner coefficient `(-4) ↦ 3` -/

private lemma coeff_lambda_sq_two [Nontrivial R] :
    (W.formalLambda ^ 2).coeff 2
      = W.formalX ^ 2
        - ((W.formalLambda - W.lambdaPrincipal).coeff 3
            + (W.formalLambda - W.lambdaPrincipal).coeff 3) := by
  set h := W.formalLambda - W.lambdaPrincipal with hh
  have hlam : W.formalLambda = W.lambdaPrincipal + h := by rw [hh]; ring
  have hh2 : (h ^ 2).coeff 2 = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    refine lt_of_lt_of_le (show ((2 : ℤ) : WithTop ℤ) < ((6 : ℤ) : WithTop ℤ) by
      exact_mod_cast (by norm_num : (2 : ℤ) < 6)) ?_
    rw [sq]
    refine le_trans ?_ HahnSeries.orderTop_add_le_mul
    rw [show ((6 : ℤ) : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) + ((3 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add W.orderTop_lambda_sub_principal W.orderTop_lambda_sub_principal
  have hLh : (W.lambdaPrincipal * h).coeff 2 = -h.coeff 3 := by
    rw [W.coeff_lambdaPrincipal_mul, show (2 : ℤ) + 1 = 3 by norm_num,
      show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 2 = 0 by norm_num,
      HahnSeries.coeff_eq_zero_of_lt_orderTop
        (lt_of_lt_of_le (show ((1 : ℤ) : WithTop ℤ) < h.orderTop from
          lt_of_lt_of_le (by exact_mod_cast (by norm_num : (1 : ℤ) < 3))
            W.orderTop_lambda_sub_principal) (le_refl _)),
      HahnSeries.coeff_eq_zero_of_lt_orderTop
        (lt_of_lt_of_le (show ((0 : ℤ) : WithTop ℤ) < h.orderTop from
          lt_of_lt_of_le (by exact_mod_cast (by norm_num : (0 : ℤ) < 3))
            W.orderTop_lambda_sub_principal) (le_refl _))]
    ring
  calc (W.formalLambda ^ 2).coeff 2
      = (W.lambdaPrincipal ^ 2 + (W.lambdaPrincipal * h + W.lambdaPrincipal * h)
          + h ^ 2).coeff 2 := by rw [hlam]; congr 1; ring
    _ = (W.lambdaPrincipal ^ 2).coeff 2
          + ((W.lambdaPrincipal * h).coeff 2 + (W.lambdaPrincipal * h).coeff 2)
          + (h ^ 2).coeff 2 := by
        rw [HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add]
    _ = W.formalX ^ 2 - (h.coeff 3 + h.coeff 3) := by rw [W.coeff_lamP_sq_two, hLh, hh2]; ring

private lemma order_formalXThree_zero [Nontrivial R] : W.formalXThree.order = 0 := by
  have hne : W.formalXThree ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [W.orderTop_formalXThree]; exact WithTop.zero_ne_top)
  have h : (W.formalXThree.order : WithTop ℤ) = (0 : WithTop ℤ) := by
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hne, W.orderTop_formalXThree]
  exact_mod_cast h

private lemma coeff_formalXThree_zero [Nontrivial R] : W.formalXThree.coeff 0 = W.formalX := by
  rw [show (0 : ℤ) = W.formalXThree.order from W.order_formalXThree_zero.symm,
    ← HahnSeries.leadingCoeff_eq, W.leadingCoeff_formalXThree]

private lemma coeff_formalXThree_two_eq [Nontrivial R] :
    W.formalXThree.coeff 2
      = W.formalX ^ 2
        - ((W.formalLambda - W.lambdaPrincipal).coeff 3
            + (W.formalLambda - W.lambdaPrincipal).coeff 3)
        + HahnSeries.C W.a₁ * (-W.formalY - HahnSeries.C W.a₁ * W.formalX)
        - HahnSeries.C (W.formalX.coeff 2) := by
  rw [formalXThree, HahnSeries.coeff_sub, HahnSeries.coeff_sub, HahnSeries.coeff_sub,
    HahnSeries.coeff_add, W.coeff_lambda_sq_two, coeff_CC_mul,
    W.coeff_lambda_eq_principal (show (2 : ℤ) < 3 by norm_num), W.coeff_lamP_two,
    coeff_CC_of_ne W.a₂ (show (2 : ℤ) ≠ 0 by norm_num),
    W.coeff_biX₁_of_ne (show (2 : ℤ) ≠ 0 by norm_num), W.coeff_biX₂]
  ring

theorem coeff_formalXThree_two_inner_neg_four [Nontrivial R] :
    (W.formalXThree.coeff 2).coeff (-4) = 3 := by
  have key := W.coeff_lam_sub_prin_three_inner
  rw [W.coeff_formalXThree_two_eq]
  set c := (W.formalLambda - W.lambdaPrincipal).coeff 3 with hc
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, HahnSeries.coeff_neg, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, sub_zero, W.coeff_formalX_sq_neg_four, key,
    W.coeff_formalX_of_lt (show (-4 : ℤ) < -2 by norm_num),
    W.coeff_formalY_of_lt (show (-4 : ℤ) < -3 by norm_num),
    HahnSeries.coeff_single_of_ne (show (-4 : ℤ) ≠ 0 by norm_num)]
  ring

theorem coeff_formalXThree_two_inner_of_lt [Nontrivial R] {g : ℤ} (hg : g < -4) :
    (W.formalXThree.coeff 2).coeff g = 0 := by
  have key := W.coeff_lam_sub_prin_three_inner_of_lt hg
  rw [W.coeff_formalXThree_two_eq]
  set c := (W.formalLambda - W.lambdaPrincipal).coeff 3 with hc
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, HahnSeries.coeff_neg, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, sub_zero, W.coeff_formalX_sq_of_lt hg, key,
    W.coeff_formalX_of_lt (show g < -2 by omega),
    W.coeff_formalY_of_lt (show g < -3 by omega),
    HahnSeries.coeff_single_of_ne (show g ≠ 0 by omega)]
  ring

/-! ### The slice `y₃.coeff 1 = x₃.coeff 2 - a₁·x₃.coeff 1` and its leading inner coefficient -/

private lemma coeff_lambda_mul_formalXThree_one [Nontrivial R] :
    (W.formalLambda * W.formalXThree).coeff 1
      = -W.formalXThree.coeff 2 - W.formalX ^ 2 := by
  set h := W.formalLambda - W.lambdaPrincipal with hh
  have hlam : W.formalLambda = W.lambdaPrincipal + h := by rw [hh]; ring
  have hhx : (h * W.formalXThree).coeff 1 = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    refine lt_of_lt_of_le (show ((1 : ℤ) : WithTop ℤ) < ((3 : ℤ) : WithTop ℤ) by
      exact_mod_cast (by norm_num : (1 : ℤ) < 3)) ?_
    have hb : ((3 : ℤ) : WithTop ℤ) ≤ h.orderTop + W.formalXThree.orderTop := by
      rw [W.orderTop_formalXThree, add_zero]; exact W.orderTop_lambda_sub_principal
    exact le_trans hb HahnSeries.orderTop_add_le_mul
  have hxm1 : W.formalXThree.coeff (-1) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (by rw [W.orderTop_formalXThree]; exact_mod_cast (by norm_num : (-1 : ℤ) < 0))
  rw [hlam, add_mul, HahnSeries.coeff_add, hhx, add_zero, W.coeff_lambdaPrincipal_mul,
    show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num,
    show (1 : ℤ) - 2 = -1 by norm_num, W.coeff_formalXThree_zero, hxm1]
  ring

private lemma coeff_formalNu_one [Nontrivial R] : W.formalNu.coeff 1 = W.formalX ^ 2 := by
  rw [formalNu, HahnSeries.coeff_sub, W.coeff_biY₁_of_ne (show (1 : ℤ) ≠ 0 by norm_num),
    show (W.formalLambda * W.biX₁).coeff 1 = W.formalLambda.coeff 1 * W.formalX by
      rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero],
    W.coeff_lambda_eq_principal (show (1 : ℤ) < 3 by norm_num), W.coeff_lamP_one]
  ring

/-- The `z₂`-degree-`1` slice of `y₃` in `R⸨z₁⸩`: `y₃.coeff 1 = x₃.coeff 2 - a₁·x₃.coeff 1`. -/
theorem coeff_formalYThree_one_eq [Nontrivial R] :
    W.formalYThree.coeff 1
      = W.formalXThree.coeff 2 - HahnSeries.C W.a₁ * W.formalXThree.coeff 1 := by
  rw [formalYThree, HahnSeries.coeff_sub, HahnSeries.coeff_sub, HahnSeries.coeff_neg,
    HahnSeries.coeff_add, W.coeff_lambda_mul_formalXThree_one, W.coeff_formalNu_one, coeff_CC_mul,
    coeff_CC_of_ne W.a₃ (show (1 : ℤ) ≠ 0 by norm_num)]
  ring

theorem coeff_formalYThree_one_inner_neg_four [Nontrivial R] :
    (W.formalYThree.coeff 1).coeff (-4) = 3 := by
  rw [W.coeff_formalYThree_one_eq, HahnSeries.coeff_sub, W.coeff_formalXThree_two_inner_neg_four,
    HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero,
    W.coeff_formalXThree_one_inner_of_lt (show (-4 : ℤ) < -3 by norm_num)]
  ring

theorem coeff_formalYThree_one_inner_of_lt [Nontrivial R] {g : ℤ} (hg : g < -4) :
    (W.formalYThree.coeff 1).coeff g = 0 := by
  rw [W.coeff_formalYThree_one_eq, HahnSeries.coeff_sub, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, sub_zero,
    W.coeff_formalXThree_one_inner_of_lt (show g < -3 by omega),
    W.coeff_formalXThree_two_inner_of_lt hg]
  ring

/-! ### `IsUnit W.formalNu`: the secant `y`-intercept is a unit of `R⸨z₁⸩⸨z₂⸩`

The `y`-intercept `ν = y₁ - λ·x₁` of the secant line through `(z₁, ·)`, `(z₂, ·)` is a unit.
Concretely its lowest `z₂`-term is `z₂⁻¹` with leading coefficient `x(z₁) = W.formalX`, itself a
unit of `R⸨z₁⸩`. This is the analytic input that makes the difference of the two `z`-plane roots
`z₂ - z₁` a unit — the missing ingredient for the `z`-cubic Vieta factorisation feeding the core
coordinate-change identity `(★)` (see `GenuineLawIdentificationCore`, the `(K1)`/`(K4)` crux). -/

/-- The coordinate series `x(z)` is a unit of `R⸨X⸩` (from `x·w = z`, i.e. `x·(w·z⁻¹) = 1`). -/
theorem isUnit_formalX : IsUnit W.formalX :=
  IsUnit.of_mul_eq_one ((W.formalW : R⸨X⸩) * HahnSeries.single (-1 : ℤ) 1) (by
    rw [← mul_assoc, W.formalX_mul_coe_formalW, HahnSeries.single_mul_single,
      show (1 : ℤ) + (-1) = 0 by norm_num, mul_one, HahnSeries.single_zero_one])

/-- The leading (`z₂`-order `-1`) coefficient of `ν = y₁ - λ·x₁` is `x(z₁) = W.formalX`. -/
private lemma coeff_formalNu_neg_one [Nontrivial R] : W.formalNu.coeff (-1) = W.formalX := by
  rw [formalNu, HahnSeries.coeff_sub, W.coeff_biY₁_of_ne (show (-1 : ℤ) ≠ 0 by norm_num),
    show (W.formalLambda * W.biX₁).coeff (-1) = W.formalLambda.coeff (-1) * W.formalX by
      rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero],
    W.coeff_lambda_eq_principal (show (-1 : ℤ) < 3 by norm_num), W.coeff_lamP_neg_one]
  ring

/-- `ν = y₁ - λ·x₁` is supported in `z₂`-degree `≥ -1`. -/
private lemma coeff_formalNu_of_lt [Nontrivial R] {g : ℤ} (hg : g < -1) :
    W.formalNu.coeff g = 0 := by
  rw [formalNu, HahnSeries.coeff_sub, W.coeff_biY₁_of_ne (show g ≠ 0 by omega),
    show (W.formalLambda * W.biX₁).coeff g = W.formalLambda.coeff g * W.formalX by
      rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero],
    W.coeff_lambda_eq_principal (show g < 3 by omega), W.coeff_lamP_of_lt hg]
  ring

/-- **`ν = formalNu` is a unit of `R⸨z₁⸩⸨z₂⸩`.** Its lowest `z₂`-term is `z₂⁻¹` with the unit
leading coefficient `x(z₁) = W.formalX`. This is the analytic input for the difference `z₂ - z₁`
of `z`-plane roots being a unit — the ingredient the `(K1)`/`(K4)` crux needs (in
`GenuineLawIdentificationCore`) for the `z`-cubic Vieta factorisation. -/
theorem isUnit_formalNu : IsUnit W.formalNu := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton _
  · have hlead : W.formalNu.coeff (-1) = W.formalX := W.coeff_formalNu_neg_one
    have hle : W.formalNu.order ≤ -1 :=
      HahnSeries.order_le_of_coeff_ne_zero (by rw [hlead]; exact W.isUnit_formalX.ne_zero)
    have hne : W.formalNu ≠ 0 := by
      intro h; rw [h, HahnSeries.coeff_zero] at hlead
      exact W.isUnit_formalX.ne_zero hlead.symm
    have hge : (-1 : ℤ) ≤ W.formalNu.order := by
      by_contra hlt
      exact HahnSeries.coeff_order_eq_zero.not.2 hne (W.coeff_formalNu_of_lt (not_le.mp hlt))
    have horder : W.formalNu.order = -1 := le_antisymm hle hge
    refine HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ ?_
    · rw [HahnSeries.leadingCoeff_eq, horder, hlead]; exact W.isUnit_formalX
    · rw [horder]; exact AddGroup.isAddUnit _

/-- The difference of the two `z`-plane base points `z₂ - z₁ ∈ R⸨z₁⸩⸨z₂⸩` satisfies
`(z₂ - z₁)·(y₂·y₁) = -ν·(x₂ - x₁)`. This is the multiplicative form of the secant-geometry identity
`z₂ - z₁ = -ν·(x₂ - x₁)·(y₁·y₂)⁻¹`: the numerator `x₁y₂ - x₂y₁` collapses to `-ν·(x₂ - x₁)` because
both points lie on the secant `y = λx + ν` (`biY₁_eq`, `biY₂_eq`), and `zᵢ·yᵢ = -xᵢ`
(`biZ₁_mul_biY₁`, `biZ₂_mul_biY₂`). -/
theorem biZ₂_sub_biZ₁_mul_biY₂_mul_biY₁ :
    (W.biZ₂ - W.biZ₁) * (W.biY₂ * W.biY₁) = -W.formalNu * (W.biX₂ - W.biX₁) := by
  linear_combination W.biY₁ * W.biZ₂_mul_biY₂ - W.biY₂ * W.biZ₁_mul_biY₁
    - W.biX₂ * W.biY₁_eq + W.biX₁ * W.biY₂_eq

/-- **The difference `z₂ - z₁` of the two `z`-plane base points is a unit of `R⸨z₁⸩⸨z₂⸩`.** Since
`(z₂ - z₁)·(y₂·y₁) = -ν·(x₂ - x₁)` (`biZ₂_sub_biZ₁_mul_biY₂_mul_biY₁`) and the right-hand side is a
unit — `ν` is a unit (`isUnit_formalNu`) and so is `x₂ - x₁` (`isUnit_biX₂_sub_biX₁`) — the factor
`z₂ - z₁` is a unit. This is the ingredient the `(K1)`/`(K4)` crux (`GenuineLawIdentificationCore`)
needs to pin the third `z`-plane root via the `z`-cubic Vieta factorisation. -/
theorem isUnit_biZ₂_sub_biZ₁ : IsUnit (W.biZ₂ - W.biZ₁) := by
  refine isUnit_of_mul_isUnit_left (y := W.biY₂ * W.biY₁) ?_
  rw [W.biZ₂_sub_biZ₁_mul_biY₂_mul_biY₁]
  exact W.isUnit_formalNu.neg.mul W.isUnit_biX₂_sub_biX₁

end WeierstrassCurve
