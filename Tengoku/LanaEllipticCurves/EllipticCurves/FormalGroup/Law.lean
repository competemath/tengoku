/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.FormalGroupLaurent
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.PowerSeriesBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extracting the Weierstrass formal group law as a bivariate power series

Building on the Laurent element `F_E = W.formalGroupLaurent = -x₃·y₃⁻¹ ∈ R⸨z₁⸩⸨z₂⸩`
(`EllipticCurves.FormalGroup.FormalGroupLaurent`) and the curve-agnostic bridge
`HahnSeries.ofDoubleLaurent : (R⸨X⸩)⸨X⸩ → MvPowerSeries (Fin 2) R`
(`EllipticCurves.FormalGroup.PowerSeriesBridge`), this file reads `F_E` off as a genuine bivariate
power series

`W.formalGroupSeries : MvPowerSeries (Fin 2) R`,

establishes the **load-bearing leading identity** `F_E.coeff 0 = z₁` — the `z₂`-degree-`0` slice of
`F_E` is exactly the inner variable `z₁` — and derives the two `z₁`-side normalisation coefficients
of `formalGroupSeries` from it:

* `constantCoeff (F_E) = 0`,
* the `z₁`-linear coefficient `coeff (single 0 1) = 1`.

Together with the `z₂`-linear coefficient `coeff (single 1 1) = 1` (which requires the inner
`z₂`-slice `F_E.coeff 1`) these are the normalisation axioms `F_E(z₁,z₂) = z₁ + z₂ + ⋯` of a formal
group law (Silverman AEC IV.1, Theorem 1.1).

## Main definitions

* `WeierstrassCurve.formalGroupSeries` : the Weierstrass formal group law read as
  `MvPowerSeries (Fin 2) R`.

## Main results

* `WeierstrassCurve.coeff_formalGroupSeries` : the bigraded coefficient bridge
  `coeff d formalGroupSeries = (F_E.coeff (d 1)).coeff (d 0)`.
* `WeierstrassCurve.coeff_formalGroupLaurent_zero` : the leading identity `F_E.coeff 0 = z₁`.
* `WeierstrassCurve.constantCoeff_formalGroupSeries` : `constantCoeff formalGroupSeries = 0`.
* `WeierstrassCurve.coeff_formalGroupSeries_single_zero` :
  `coeff (single 0 1) formalGroupSeries = 1`.
* `WeierstrassCurve.coeff_formalGroupSeries_single_one` :
  `coeff (single 1 1) formalGroupSeries = 1` (the `z₂`-linear normalisation coefficient).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The load-bearing leading identity `F_E.coeff 0 = z₁` -/

/-- The `z₂`-order of `x₃` and `y₃`, and of `F_E`, are all `0` over a nontrivial ring, so the
associated `HahnSeries.order` (the `ℤ`-valued order) is `0`. -/
private lemma order_formalYThree [Nontrivial R] : W.formalYThree.order = 0 := by
  have hne : W.formalYThree ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [W.orderTop_formalYThree]; exact WithTop.zero_ne_top)
  have h := HahnSeries.order_eq_orderTop_of_ne_zero hne
  rw [W.orderTop_formalYThree] at h
  exact_mod_cast h

private lemma order_formalXThree [Nontrivial R] : W.formalXThree.order = 0 := by
  have hne : W.formalXThree ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [W.orderTop_formalXThree]; exact WithTop.zero_ne_top)
  have h := HahnSeries.order_eq_orderTop_of_ne_zero hne
  rw [W.orderTop_formalXThree] at h
  exact_mod_cast h

private lemma order_formalGroupLaurent [Nontrivial R] : W.formalGroupLaurent.order = 0 := by
  have hne : W.formalGroupLaurent ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp
      (by rw [W.orderTop_formalGroupLaurent]; exact WithTop.zero_ne_top)
  have h := HahnSeries.order_eq_orderTop_of_ne_zero hne
  rw [W.orderTop_formalGroupLaurent] at h
  exact_mod_cast h

/-- **The load-bearing leading identity.** The `z₂`-degree-`0` slice of the formal group law `F_E`
is exactly the inner variable `z₁ = single 1 1 ∈ R⸨z₁⸩`.

Take the `z₂`-order-`0` leading coefficient of the defining identity `F_E · y₃ = -x₃`: both `F_E`
and `y₃` have `z₂`-order `0`, so the `z₂`-degree-`0` coefficient of the product is
`F_E.coeff 0 · y₃.coeff 0 = F_E.coeff 0 · y(z₁)` (`leadingCoeff_formalYThree`), while the right side
is `-x₃.coeff 0 = -x(z₁)` (`leadingCoeff_formalXThree`). Since `z₁ · y(z₁) = -x(z₁)`
(`single_one_mul_formalY`) and `y(z₁)` is a unit (`isUnit_formalY`), cancelling `y(z₁)` gives
`F_E.coeff 0 = z₁`. This pins the inner behaviour of the leading `z₂`-slice to a pole-free
monomial. -/
theorem coeff_formalGroupLaurent_zero :
    W.formalGroupLaurent.coeff 0 = HahnSeries.single (1 : ℤ) 1 := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  -- The `z₂`-degree-`0` coefficient of `F_E · y₃` is the product of the two leading coefficients.
  have hx3 : W.formalXThree.coeff 0 = W.formalX := by
    rw [← W.order_formalXThree, ← HahnSeries.leadingCoeff_eq, W.leadingCoeff_formalXThree]
  have hmul := HahnSeries.coeff_mul_order_add_order W.formalGroupLaurent W.formalYThree
  rw [W.order_formalGroupLaurent, W.order_formalYThree, add_zero, W.leadingCoeff_formalYThree,
    HahnSeries.leadingCoeff_eq, W.order_formalGroupLaurent,
    W.formalGroupLaurent_mul_formalYThree, HahnSeries.coeff_neg, hx3] at hmul
  -- `hmul : -x(z₁) = F_E.coeff 0 · y(z₁)`; combine with `z₁ · y(z₁) = -x(z₁)` and cancel `y(z₁)`.
  have hkey : W.formalGroupLaurent.coeff 0 * W.formalY
      = HahnSeries.single (1 : ℤ) 1 * W.formalY := by
    rw [← hmul, W.single_one_mul_formalY]
  exact (W.isUnit_formalY.mul_left_inj).mp hkey

/-! ### The formal group series and its `z₁`-side normalisation coefficients -/

/-- The **Weierstrass formal group law** read as a genuine bivariate power series
`MvPowerSeries (Fin 2) R`, via the bridge `HahnSeries.ofDoubleLaurent` applied to the Laurent
element `F_E = W.formalGroupLaurent`. (Silverman AEC IV.1, Theorem 1.1.) -/
noncomputable def formalGroupSeries : MvPowerSeries (Fin 2) R :=
  HahnSeries.ofDoubleLaurent W.formalGroupLaurent

/-- The bigraded coefficient bridge: the coefficient of `z₁^(d 0) z₂^(d 1)` in `formalGroupSeries`
is the inner `z₁`-coefficient `(F_E.coeff (d 1)).coeff (d 0)` of the Laurent element `F_E`. -/
theorem coeff_formalGroupSeries (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d W.formalGroupSeries
      = (W.formalGroupLaurent.coeff (d 1 : ℤ)).coeff (d 0 : ℤ) :=
  HahnSeries.coeff_ofDoubleLaurent _ _

/-- **Normalisation axiom (constant term).** `F_E` has zero constant term: `constantCoeff = 0`. -/
theorem constantCoeff_formalGroupSeries :
    MvPowerSeries.constantCoeff W.formalGroupSeries = 0 := by
  rw [formalGroupSeries, HahnSeries.constantCoeff_ofDoubleLaurent, W.coeff_formalGroupLaurent_zero,
    HahnSeries.coeff_single_of_ne (by norm_num)]

/-- **Normalisation axiom (`z₁`-linear term).** The coefficient of `z₁` in `F_E` is `1`. -/
theorem coeff_formalGroupSeries_single_zero :
    MvPowerSeries.coeff (Finsupp.single 0 1) W.formalGroupSeries = 1 := by
  rw [formalGroupSeries, HahnSeries.coeff_ofDoubleLaurent_single_zero,
    W.coeff_formalGroupLaurent_zero, Nat.cast_one, HahnSeries.coeff_single_same]

/-! ### The `z₂`-linear normalisation coefficient `coeff (single 1 1) = 1` -/

/-- Removing the leading (degree-`0`) term of a `z₂`-order-`0` series raises the order to `≥ 1`. -/
private lemma orderTop_sub_leading_ge [Nontrivial R] {x : (R⸨X⸩)⸨X⸩}
    (hx : x.orderTop = (0 : WithTop ℤ)) :
    ((1 : ℤ) : WithTop ℤ) ≤ (x - HahnSeries.single 0 (x.coeff 0)).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  have hg1 : g < 1 := by exact_mod_cast hg
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single]
  by_cases hg0 : g = 0
  · rw [hg0, ite_eq_left rfl, sub_self]
  · rw [ite_eq_right hg0, HahnSeries.coeff_eq_zero_of_lt_orderTop
      (by rw [hx]; exact_mod_cast (show g < 0 by omega)), sub_zero]

/-- The `z₂`-degree-`1` coefficient of a product of two `z₂`-order-`0` series, as the convolution
over the two contributing pairs `(0,1)` and `(1,0)`. -/
private lemma coeff_mul_one_of_orderTop_zero [Nontrivial R] {a b : (R⸨X⸩)⸨X⸩}
    (ha : a.orderTop = (0 : WithTop ℤ)) (hb : b.orderTop = (0 : WithTop ℤ)) :
    (a * b).coeff 1 = a.coeff 1 * b.coeff 0 + a.coeff 0 * b.coeff 1 := by
  have hb' : ((1 : ℤ) : WithTop ℤ) ≤ (b - HahnSeries.single 0 (b.coeff 0)).orderTop :=
    orderTop_sub_leading_ge hb
  have ha' : ((1 : ℤ) : WithTop ℤ) ≤ (a - HahnSeries.single 0 (a.coeff 0)).orderTop :=
    orderTop_sub_leading_ge ha
  have hvanish : ((a - HahnSeries.single 0 (a.coeff 0))
      * (b - HahnSeries.single 0 (b.coeff 0))).coeff 1 = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    refine lt_of_lt_of_le (show ((1 : ℤ) : WithTop ℤ) < ((2 : ℤ) : WithTop ℤ) by
      exact_mod_cast (by norm_num : (1 : ℤ) < 2)) ?_
    refine le_trans ?_ HahnSeries.orderTop_add_le_mul
    rw [show ((2 : ℤ) : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add ha' hb'
  have ha1 : (a - HahnSeries.single 0 (a.coeff 0)).coeff 1 = a.coeff 1 := by
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_of_ne (by norm_num : (1 : ℤ) ≠ 0), sub_zero]
  have hexpand : a * b = HahnSeries.single 0 (a.coeff 0) * b
      + (a - HahnSeries.single 0 (a.coeff 0)) * (HahnSeries.single 0 (b.coeff 0))
      + (a - HahnSeries.single 0 (a.coeff 0)) * (b - HahnSeries.single 0 (b.coeff 0)) := by ring
  rw [hexpand, HahnSeries.coeff_add, HahnSeries.coeff_add, hvanish, add_zero,
    HahnSeries.coeff_single_zero_mul, HahnSeries.coeff_mul_single_zero, ha1]
  ring

/-- The leading `z₂`-coefficient of `y₃` sits in `z₂`-degree `0`: `y₃.coeff 0 = y(z₁)`. -/
private lemma coeff_formalYThree_zero [Nontrivial R] : W.formalYThree.coeff 0 = W.formalY := by
  have hne : W.formalYThree ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [W.orderTop_formalYThree]; exact WithTop.zero_ne_top)
  have hord : W.formalYThree.order = 0 := by
    have h : (W.formalYThree.order : WithTop ℤ) = (0 : WithTop ℤ) := by
      rw [HahnSeries.order_eq_orderTop_of_ne_zero hne, W.orderTop_formalYThree]
    exact_mod_cast h
  rw [show (0 : ℤ) = W.formalYThree.order from hord.symm, ← HahnSeries.leadingCoeff_eq,
    W.leadingCoeff_formalYThree]

/-! Order and leading coefficient of the coerced coordinate series `w(z₁) ∈ R⸨z₁⸩`. -/

private lemma coeff_coe_formalW_of_lt {g : ℤ} (hg : g < 3) : (W.formalW : R⸨X⸩).coeff g = 0 := by
  rcases lt_or_ge g 0 with hlt | hge
  · exact coe_powerSeries_coeff_of_neg _ hlt
  · lift g to ℕ using hge with n
    rw [LaurentSeries.coeff_coe_powerSeries]
    exact PowerSeries.coeff_of_lt_order n
      (lt_of_lt_of_le (by exact_mod_cast (show n < 3 by exact_mod_cast hg)) W.order_formalW)

private lemma coeff_coe_formalW_three : (W.formalW : R⸨X⸩).coeff 3 = 1 := by
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from by norm_num, LaurentSeries.coeff_coe_powerSeries,
    W.coeff_formalW_three]

private lemma coe_formalW_ne_zero [Nontrivial R] : (W.formalW : R⸨X⸩) ≠ 0 :=
  HahnSeries.orderTop_ne_top.mp (by
    rw [show (W.formalW : R⸨X⸩).orderTop = ((3 : ℤ) : WithTop ℤ) from ?_]
    · exact WithTop.coe_ne_top
    · refine le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero ?_) ?_
      · rw [W.coeff_coe_formalW_three]; exact one_ne_zero
      · rw [HahnSeries.le_orderTop_iff_forall]
        intro j hj
        exact W.coeff_coe_formalW_of_lt (by exact_mod_cast hj))

private lemma order_coe_formalW [Nontrivial R] : (W.formalW : R⸨X⸩).order = 3 := by
  have hot : (W.formalW : R⸨X⸩).orderTop = ((3 : ℤ) : WithTop ℤ) := by
    refine le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero ?_) ?_
    · rw [W.coeff_coe_formalW_three]; exact one_ne_zero
    · rw [HahnSeries.le_orderTop_iff_forall]
      intro j hj
      exact W.coeff_coe_formalW_of_lt (by exact_mod_cast hj)
  have h : ((W.formalW : R⸨X⸩).order : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) := by
    rw [HahnSeries.order_eq_orderTop_of_ne_zero W.coe_formalW_ne_zero, hot]
  exact_mod_cast h

/-- **The load-bearing `z₂`-linear identity.** The `z₁`-constant part of the `z₂`-degree-`1` slice
of `F_E` is `1`: the coefficient of `z₂` in `F_E = z₁ + z₂ - a₁z₁z₂ - ⋯` is `1` at `z₁`-degree `0`.

Take the `z₂`-degree-`1` coefficient of the defining identity `F_E · y₃ = -x₃` (both factors have
`z₂`-order `0`): `F_E.coeff 1 · y(z₁) = -x₃.coeff 1 - z₁·y₃.coeff 1 =: R`. Since `y(z₁)` is the unit
with inverse `-w(z₁)`, `F_E.coeff 1 = R·(-w(z₁))`. The slices `x₃.coeff 1` (inner order `-3`, lead
`-2`) and `y₃.coeff 1` (inner order `-4`, lead `3`) give `R` inner order `-3` with leading
coefficient `-1`; `w(z₁)` has inner order `3` with leading coefficient `1`, so the product's
`z₁`-degree-`0` coefficient is `(-1)·(-1) = 1`. (Silverman AEC IV.1, Theorem 1.1.) -/
theorem coeff_formalGroupLaurent_one_inner_zero [Nontrivial R] :
    (W.formalGroupLaurent.coeff 1).coeff 0 = 1 := by
  -- The `z₂`-degree-`1` coefficient of `F_E · y₃ = -x₃`.
  have hmaster := coeff_mul_one_of_orderTop_zero W.orderTop_formalGroupLaurent
    W.orderTop_formalYThree
  rw [W.formalGroupLaurent_mul_formalYThree, HahnSeries.coeff_neg, W.coeff_formalGroupLaurent_zero,
    W.coeff_formalYThree_zero] at hmaster
  -- Solve for `F_E.coeff 1 · y(z₁) = R`.
  set Rr := -W.formalXThree.coeff 1 - HahnSeries.single (1 : ℤ) 1 * W.formalYThree.coeff 1 with hRr
  have hFEmul : W.formalGroupLaurent.coeff 1 * W.formalY = Rr := by
    rw [hRr]; linear_combination -hmaster
  -- Invert the unit `y(z₁)` (inverse `-w(z₁)`).
  have hinv : W.formalGroupLaurent.coeff 1 = Rr * (-(W.formalW : R⸨X⸩)) := by
    have h1 : W.formalY * (-(W.formalW : R⸨X⸩)) = 1 := by
      rw [mul_neg, W.formalY_mul_coe_formalW, neg_neg]
    calc W.formalGroupLaurent.coeff 1
        = W.formalGroupLaurent.coeff 1 * W.formalY * (-(W.formalW : R⸨X⸩)) := by
          rw [mul_assoc, h1, mul_one]
      _ = Rr * (-(W.formalW : R⸨X⸩)) := by rw [hFEmul]
  -- Leading `z₁`-behaviour of `R`.
  have hRrcoeff : Rr.coeff (-3) = -1 := by
    rw [hRr, HahnSeries.coeff_sub, HahnSeries.coeff_neg, W.coeff_formalXThree_one_inner_neg_three,
      HahnSeries.coeff_single_mul, show (-3 : ℤ) - 1 = -4 by norm_num,
      W.coeff_formalYThree_one_inner_neg_four]
    ring
  have hRrlt : ∀ g < (-3 : ℤ), Rr.coeff g = 0 := by
    intro g hg
    rw [hRr, HahnSeries.coeff_sub, HahnSeries.coeff_neg,
      W.coeff_formalXThree_one_inner_of_lt hg, HahnSeries.coeff_single_mul,
      W.coeff_formalYThree_one_inner_of_lt (show g - 1 < -4 by omega)]
    ring
  have hRr_ne : Rr ≠ 0 := by
    intro h
    have hc : Rr.coeff (-3) = 0 := by rw [h]; simp
    rw [hRrcoeff] at hc
    exact one_ne_zero (neg_eq_zero.mp hc)
  have horderRr : Rr.order = -3 := by
    have hot : Rr.orderTop = ((-3 : ℤ) : WithTop ℤ) := by
      refine le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero ?_) ?_
      · rw [hRrcoeff]; exact neg_ne_zero.mpr one_ne_zero
      · rw [HahnSeries.le_orderTop_iff_forall]
        intro j hj
        exact hRrlt j (by exact_mod_cast hj)
    have h : (Rr.order : WithTop ℤ) = ((-3 : ℤ) : WithTop ℤ) := by
      rw [HahnSeries.order_eq_orderTop_of_ne_zero hRr_ne, hot]
    exact_mod_cast h
  have hRrlead : Rr.leadingCoeff = -1 := by rw [HahnSeries.leadingCoeff_eq, horderRr, hRrcoeff]
  -- Leading `z₁`-behaviour of `-w(z₁)`.
  have hwlead : (-(W.formalW : R⸨X⸩)).leadingCoeff = -1 := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.order_neg, W.order_coe_formalW,
      HahnSeries.coeff_neg, W.coeff_coe_formalW_three]
  -- Extract the `z₁`-degree-`0` coefficient of the product `R·(-w(z₁))`.
  have h := HahnSeries.coeff_mul_order_add_order Rr (-(W.formalW : R⸨X⸩))
  rw [horderRr, HahnSeries.order_neg, W.order_coe_formalW, show (-3 : ℤ) + 3 = 0 by norm_num,
    hRrlead, hwlead, ← hinv] at h
  rw [h]; ring

/-- **Normalisation axiom (`z₂`-linear term).** The coefficient of `z₂` in `F_E` is `1`.
Together with `constantCoeff = 0` and `coeff (single 0 1) = 1` these are the normalisation axioms
`F_E(z₁, z₂) = z₁ + z₂ + ⋯` of a formal group law (Silverman AEC IV.1, Theorem 1.1). -/
theorem coeff_formalGroupSeries_single_one :
    MvPowerSeries.coeff (Finsupp.single 1 1) W.formalGroupSeries = 1 := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  rw [formalGroupSeries, HahnSeries.coeff_ofDoubleLaurent_single_one]
  exact W.coeff_formalGroupLaurent_one_inner_zero

end WeierstrassCurve
