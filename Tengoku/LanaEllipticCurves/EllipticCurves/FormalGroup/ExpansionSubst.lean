/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.Expansion
import Tengoku.Seed.RingTheory.MvPowerSeries.Order
import Tengoku.Seed.RingTheory.PowerSeries.Substitution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parametrised uniqueness of the Weierstrass expansion

Fix a Weierstrass curve `W` over a `CommRing R` and a parameter multivariate power series
`t : MvPowerSeries τ R` of positive order (`1 ≤ t.order`, equivalently `constantCoeff t = 0`).
Substituting `X ↦ t` into the order-increasing operator `W.wOp` of
`EllipticCurves.FormalGroup.Expansion` gives the *parametrised* operator

`W.wOpSubst t u = t³ + (a₁t + a₂t²) u + (a₃ + a₄t) u² + a₆ u³`

on `MvPowerSeries τ R`. This file proves the bivariate analogue of the univariate uniqueness theorem
`WeierstrassCurve.eq_formalW_of_wOp_fixed`: `W.formalW.subst t` is the **unique** power series of
positive order fixed by `W.wOpSubst t`.

The proof is a direct port of the univariate argument (`Expansion.lean`): the contraction estimate
`order_wOpSubst_sub` — applying `W.wOpSubst t` increases the order of agreement by one — is proved
from the multiplicativity/additivity bounds on `MvPowerSeries.order`, and the fixed point
`W.formalW.subst t` is obtained by pushing `formalW_eq` through the substitution `AlgHom`.

## Main definitions

* `WeierstrassCurve.wOpSubst` : the operator `W.wOp` with local parameter `X` replaced by `t`.

## Main results

* `WeierstrassCurve.order_wOpSubst_sub` : the contraction estimate.
* `WeierstrassCurve.formalW_subst_wOpSubst_fixed` : `W.formalW.subst t` is a fixed point.
* `WeierstrassCurve.one_le_order_formalW_subst` : it has positive order.
* `WeierstrassCurve.wOpSubst_fixed_unique` : any two positive-order fixed points agree.
* `WeierstrassCurve.eq_formalW_subst_of_wOpSubst_fixed` : any positive-order fixed point of
  `W.wOpSubst t` equals `W.formalW.subst t`.

This is the parametrised uniqueness input for route 1 of the inner pole-freeness of the Weierstrass
formal group law `F_E` (Silverman, *The Arithmetic of Elliptic Curves*, IV.1): specialised at
`τ = Fin 2`, `t = W.formalGroupSeries`, it identifies the transported `W₃ = -y₃⁻¹` with
`formalW ∘ F_E`, exhibiting `F_E` as pole-free.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {τ : Type*}

/-- The operator `W.wOp` with the local parameter `X` replaced by a parameter series
`t : MvPowerSeries τ R`: `W.wOpSubst t u = t³ + (a₁t + a₂t²) u + (a₃ + a₄t) u² + a₆ u³`. Its unique
positive-order fixed point (for `t` of positive order) is `W.formalW.subst t`. -/
noncomputable def wOpSubst (t u : MvPowerSeries τ R) : MvPowerSeries τ R :=
  t ^ 3 + (MvPowerSeries.C W.a₁ * t + MvPowerSeries.C W.a₂ * t ^ 2) * u
    + (MvPowerSeries.C W.a₃ + MvPowerSeries.C W.a₄ * t) * u ^ 2 + MvPowerSeries.C W.a₆ * u ^ 3

/-- A three-term sum of `MvPowerSeries` has order at least `k` if each summand does. -/
private lemma mvOrder_add₃_ge {a b c : MvPowerSeries τ R} {k : ℕ∞}
    (ha : k ≤ a.order) (hb : k ≤ b.order) (hc : k ≤ c.order) : k ≤ (a + b + c).order :=
  le_trans (le_min (le_min ha hb) hc)
    (le_trans (min_le_min MvPowerSeries.min_order_le_add le_rfl) MvPowerSeries.min_order_le_add)

/-- The key contraction estimate: applying `W.wOpSubst t` increases the order of agreement by one.
If `t, u, v` have positive order and `u, v` agree up to order `m`, then `W.wOpSubst t u` and
`W.wOpSubst t v` agree up to order `m + 1`. -/
lemma order_wOpSubst_sub {t : MvPowerSeries τ R} (ht : 1 ≤ t.order) (u v : MvPowerSeries τ R)
    (hu : 1 ≤ u.order) (hv : 1 ≤ v.order) {m : ℕ} (hm : (m : ℕ∞) ≤ (u - v).order) :
    (m : ℕ∞) + 1 ≤ (W.wOpSubst t u - W.wOpSubst t v).order := by
  have hct : MvPowerSeries.constantCoeff t = 0 :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp ht
  have hcu : MvPowerSeries.constantCoeff u = 0 :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp hu
  have hcv : MvPowerSeries.constantCoeff v = 0 :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp hv
  -- factor the difference; the `t³` base term cancels
  have hfac : W.wOpSubst t u - W.wOpSubst t v =
      (MvPowerSeries.C W.a₁ * t + MvPowerSeries.C W.a₂ * t ^ 2) * (u - v)
        + (MvPowerSeries.C W.a₃ + MvPowerSeries.C W.a₄ * t) * ((u + v) * (u - v))
        + MvPowerSeries.C W.a₆ * ((u ^ 2 + u * v + v ^ 2) * (u - v)) := by
    simp only [wOpSubst]; ring
  rw [hfac]
  -- the parameter factor and the auxiliary factors all have order at least `1`
  have hP₁ : (1 : ℕ∞) ≤ (MvPowerSeries.C W.a₁ * t + MvPowerSeries.C W.a₂ * t ^ 2).order := by
    rw [MvPowerSeries.one_le_order_iff_constCoeff_eq_zero]
    simp [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, hct]
  have huv : (1 : ℕ∞) ≤ (u + v).order := by
    rw [MvPowerSeries.one_le_order_iff_constCoeff_eq_zero]
    simp [map_add, hcu, hcv]
  have huv2 : (1 : ℕ∞) ≤ (u ^ 2 + u * v + v ^ 2).order := by
    rw [MvPowerSeries.one_le_order_iff_constCoeff_eq_zero]
    simp [map_add, map_mul, map_pow, hcu, hcv]
  refine mvOrder_add₃_ge ?_ ?_ ?_
  · -- term 1: order ≥ order(a₁t + a₂t²) + order(u - v) ≥ 1 + m
    calc (m : ℕ∞) + 1 = 1 + m := by rw [add_comm]
      _ ≤ (MvPowerSeries.C W.a₁ * t + MvPowerSeries.C W.a₂ * t ^ 2).order + (u - v).order :=
          add_le_add hP₁ hm
      _ ≤ _ := MvPowerSeries.le_order_mul
  · -- term 2: order ≥ 0 + (order(u + v) + order(u - v)) ≥ 1 + m
    calc (m : ℕ∞) + 1 = 0 + (1 + m) := by rw [zero_add, add_comm]
      _ ≤ (MvPowerSeries.C W.a₃ + MvPowerSeries.C W.a₄ * t).order
            + ((u + v).order + (u - v).order) := add_le_add zero_le (add_le_add huv hm)
      _ ≤ (MvPowerSeries.C W.a₃ + MvPowerSeries.C W.a₄ * t).order + ((u + v) * (u - v)).order :=
          add_le_add le_rfl MvPowerSeries.le_order_mul
      _ ≤ _ := MvPowerSeries.le_order_mul
  · -- term 3: order ≥ 0 + (order(u² + uv + v²) + order(u - v)) ≥ 1 + m
    calc (m : ℕ∞) + 1 = 0 + (1 + m) := by rw [zero_add, add_comm]
      _ ≤ (MvPowerSeries.C W.a₆).order + ((u ^ 2 + u * v + v ^ 2).order + (u - v).order) :=
          add_le_add zero_le (add_le_add huv2 hm)
      _ ≤ (MvPowerSeries.C W.a₆).order + ((u ^ 2 + u * v + v ^ 2) * (u - v)).order :=
          add_le_add le_rfl MvPowerSeries.le_order_mul
      _ ≤ _ := MvPowerSeries.le_order_mul

/-- `W.formalW.subst t` is a fixed point of the parametrised operator `W.wOpSubst t`. This is the
image of the univariate fixed-point equation `formalW_eq` under the substitution `AlgHom`. -/
theorem formalW_subst_wOpSubst_fixed {t : MvPowerSeries τ R} (ht : 1 ≤ t.order) :
    W.formalW.subst t = W.wOpSubst t (W.formalW.subst t) := by
  have hct : MvPowerSeries.constantCoeff t = 0 :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp ht
  have ha : PowerSeries.HasSubst t := PowerSeries.HasSubst.of_constantCoeff_zero hct
  conv_lhs => rw [W.formalW_eq]
  simp only [wOp, wOpSubst, PowerSeries.subst_add ha, PowerSeries.subst_mul ha,
    PowerSeries.subst_pow ha, PowerSeries.subst_X ha, PowerSeries.subst_C]

/-- `W.formalW.subst t` has positive order (indeed order at least `3`, inherited from `formalW`). -/
theorem one_le_order_formalW_subst {t : MvPowerSeries τ R} (ht : 1 ≤ t.order) :
    1 ≤ (W.formalW.subst t).order := by
  have hct : MvPowerSeries.constantCoeff t = 0 :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp ht
  have h1 : (1 : ℕ∞) ≤ W.formalW.order :=
    le_trans (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)) W.order_formalW
  exact le_trans h1 (PowerSeries.le_order_subst_left hct)

/-- **Parametrised uniqueness of the Weierstrass expansion.** For `t` of positive order, the
operator `W.wOpSubst t` has at most one fixed point of positive order: if `u, v` both have positive
order and are fixed by `W.wOpSubst t`, then `u = v`. -/
theorem wOpSubst_fixed_unique {t : MvPowerSeries τ R} (ht : 1 ≤ t.order)
    {u v : MvPowerSeries τ R} (hu : 1 ≤ u.order) (hv : 1 ≤ v.order)
    (hfu : u = W.wOpSubst t u) (hfv : v = W.wOpSubst t v) : u = v := by
  -- `u` and `v` agree to every finite order, so their difference is `0`.
  have key : ∀ m : ℕ, (m : ℕ∞) ≤ (u - v).order := by
    intro m
    induction m with
    | zero => exact_mod_cast zero_le
    | succ k ih =>
      have h := W.order_wOpSubst_sub ht u v hu hv ih
      rw [← hfu, ← hfv] at h
      rw [Nat.cast_succ]
      exact h
  refine sub_eq_zero.mp (MvPowerSeries.ext fun n => ?_)
  rw [map_zero]
  refine MvPowerSeries.coeff_of_lt_order ?_
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self (Finsupp.degree n))
    (key (Finsupp.degree n + 1))

/-- **Parametrised uniqueness (headline form).** Any positive-order fixed point of `W.wOpSubst t`
(for `t` of positive order) equals `W.formalW.subst t`. This is the bivariate companion of
`WeierstrassCurve.eq_formalW_of_wOp_fixed`. -/
theorem eq_formalW_subst_of_wOpSubst_fixed {t : MvPowerSeries τ R} (ht : 1 ≤ t.order)
    {u : MvPowerSeries τ R} (hu : 1 ≤ u.order) (hfix : u = W.wOpSubst t u) :
    u = W.formalW.subst t :=
  W.wOpSubst_fixed_unique ht hu (W.one_le_order_formalW_subst ht) hfix
    (W.formalW_subst_wOpSubst_fixed ht)

end WeierstrassCurve
