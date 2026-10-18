/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.Seed.RingTheory.PowerSeries.Order
import Tengoku.Seed.RingTheory.PowerSeries.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Weierstrass formal expansion `w(z)` near the origin

Given a Weierstrass curve `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆`, substituting the local
parameter `z = -x/y` (so `x = z/w`, `y = -1/w`) into the Weierstrass equation yields the
fixed-point equation (Silverman, *The Arithmetic of Elliptic Curves*, IV.1.1)
$$ w = z^3 + (a_1 z + a_2 z^2) w + (a_3 + a_4 z) w^2 + a_6 w^3. $$
This file constructs the unique power series `w ∈ R⟦z⟧` solving this equation, as the
`z`-adic limit of the iteration `wₙ₊₁ = T(wₙ)` starting from `w₀ = 0`, where `T` is the
order-increasing operator on the right-hand side.

## Main definitions

* `WeierstrassCurve.wOp` : the operator `T` on `R⟦X⟧`.
* `WeierstrassCurve.wIter` : the sequence of approximations `w₀ = 0`, `wₙ₊₁ = T(wₙ)`.
* `WeierstrassCurve.formalW` : the Weierstrass expansion `w(z) ∈ R⟦X⟧`.

## Main results

* `WeierstrassCurve.formalW_eq` : `w` satisfies the fixed-point / functional equation.
* `WeierstrassCurve.order_formalW` : `3 ≤ order w`, i.e. `w = c₃ z³ + …`.
* `WeierstrassCurve.coeff_formalW_three` : the leading coefficient is `1`, so `w = z³ + …`.

The coordinate series `x(z) = z / w` and `y(z) = -1 / w` — which have poles at the origin and so
naturally live in the Laurent series ring `R⸨X⸩` — are built on top of `formalW` in
`EllipticCurves.FormalGroup.CoordinateSeries`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

namespace WeierstrassCurve

open PowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The operator `T u = z³ + (a₁z + a₂z²) u + (a₃ + a₄z) u² + a₆ u³` whose unique
positive-order fixed point is the Weierstrass expansion `w(z)`. -/
noncomputable def wOp (u : R⟦X⟧) : R⟦X⟧ :=
  X ^ 3 + (C W.a₁ * X + C W.a₂ * X ^ 2) * u
    + (C W.a₃ + C W.a₄ * X) * u ^ 2 + C W.a₆ * u ^ 3

/-- The sequence of approximations to `w(z)`: `w₀ = 0`, `wₙ₊₁ = T(wₙ)`. -/
noncomputable def wIter (W : WeierstrassCurve R) : ℕ → R⟦X⟧
  | 0 => 0
  | (n + 1) => W.wOp (W.wIter n)

@[simp] lemma wIter_zero : W.wIter 0 = 0 := rfl

@[simp] lemma wIter_succ (n : ℕ) : W.wIter (n + 1) = W.wOp (W.wIter n) := rfl

/-- A three-term sum has order at least `k` if each summand does. -/
private lemma order_add₃_ge {a b c : R⟦X⟧} {k : ℕ∞}
    (ha : k ≤ a.order) (hb : k ≤ b.order) (hc : k ≤ c.order) : k ≤ (a + b + c).order :=
  le_trans (le_min (le_min ha hb) hc)
    (le_trans (min_le_min (min_order_le_order_add a b) le_rfl)
      (min_order_le_order_add (a + b) c))

/-- A four-term sum has order at least `k` if each summand does. -/
private lemma order_add₄_ge {a b c d : R⟦X⟧} {k : ℕ∞}
    (ha : k ≤ a.order) (hb : k ≤ b.order) (hc : k ≤ c.order) (hd : k ≤ d.order) :
    k ≤ (a + b + c + d).order :=
  le_trans (le_min (order_add₃_ge ha hb hc) hd) (min_order_le_order_add (a + b + c) d)

/-- The constant coefficient of `P₁ = a₁z + a₂z²` is zero, so `1 ≤ order P₁`. -/
private lemma one_le_order_P₁ : 1 ≤ (C W.a₁ * X + C W.a₂ * X ^ 2 : R⟦X⟧).order := by
  rw [one_le_order_iff_constCoeff_eq_zero]
  simp

private lemma one_le_order_of_constCoeff_zero {φ : R⟦X⟧} (h : constantCoeff φ = 0) :
    1 ≤ φ.order :=
  one_le_order_iff_constCoeff_eq_zero.mpr h

private lemma constCoeff_eq_zero_of_one_le_order {φ : R⟦X⟧} (h : 1 ≤ φ.order) :
    constantCoeff φ = 0 :=
  one_le_order_iff_constCoeff_eq_zero.mp h

/-- If the right factor has order at least `k`, so does the product. -/
private lemma le_order_mul_right {a b : R⟦X⟧} {k : ℕ∞} (hb : k ≤ b.order) :
    k ≤ (a * b).order :=
  hb.trans (le_add_self.trans (le_order_mul a b))

/-- The key contraction estimate: applying `T` increases the order of agreement by one.
If `u, v` have positive order and agree up to order `m`, then `T u, T v` agree up to
order `m + 1`. -/
lemma order_wOp_sub (u v : R⟦X⟧) (hu : 1 ≤ u.order) (hv : 1 ≤ v.order) {m : ℕ}
    (hm : (m : ℕ∞) ≤ (u - v).order) : (m : ℕ∞) + 1 ≤ (W.wOp u - W.wOp v).order := by
  have hcu : constantCoeff u = 0 := constCoeff_eq_zero_of_one_le_order hu
  have hcv : constantCoeff v = 0 := constCoeff_eq_zero_of_one_le_order hv
  -- factor the difference
  have hfac : W.wOp u - W.wOp v =
      (C W.a₁ * X + C W.a₂ * X ^ 2) * (u - v)
        + (C W.a₃ + C W.a₄ * X) * ((u + v) * (u - v))
        + C W.a₆ * ((u ^ 2 + u * v + v ^ 2) * (u - v)) := by
    simp only [wOp]; ring
  rw [hfac]
  -- order of `u + v` and `u² + uv + v²` are at least 1
  have huv : (1 : ℕ∞) ≤ (u + v).order := by
    refine one_le_order_of_constCoeff_zero ?_
    simp [hcu, hcv]
  have huv2 : (1 : ℕ∞) ≤ (u ^ 2 + u * v + v ^ 2).order := by
    refine one_le_order_of_constCoeff_zero ?_
    simp [hcu, hcv]
  refine order_add₃_ge ?_ ?_ ?_
  · -- term 1: order ≥ order P₁ + order (u - v) ≥ 1 + m
    calc (m : ℕ∞) + 1 = 1 + m := by rw [add_comm]
      _ ≤ (C W.a₁ * X + C W.a₂ * X ^ 2).order + (u - v).order :=
          add_le_add W.one_le_order_P₁ hm
      _ ≤ _ := le_order_mul _ _
  · -- term 2: order ≥ 0 + (order (u + v) + order (u - v)) ≥ 1 + m
    calc (m : ℕ∞) + 1 = 0 + (1 + m) := by rw [zero_add, add_comm]
      _ ≤ (C W.a₃ + C W.a₄ * X).order + ((u + v).order + (u - v).order) :=
          add_le_add (zero_le) (add_le_add huv hm)
      _ ≤ (C W.a₃ + C W.a₄ * X).order + ((u + v) * (u - v)).order :=
          add_le_add le_rfl (le_order_mul _ _)
      _ ≤ _ := le_order_mul _ _
  · -- term 3: order ≥ 0 + (order (u²+uv+v²) + order (u - v)) ≥ 1 + m
    calc (m : ℕ∞) + 1 = 0 + (1 + m) := by rw [zero_add, add_comm]
      _ ≤ (C W.a₆).order + ((u ^ 2 + u * v + v ^ 2).order + (u - v).order) :=
          add_le_add (zero_le) (add_le_add huv2 hm)
      _ ≤ (C W.a₆).order + ((u ^ 2 + u * v + v ^ 2) * (u - v)).order :=
          add_le_add le_rfl (le_order_mul _ _)
      _ ≤ _ := le_order_mul _ _

/-- Each approximation `wₙ` has order at least `3` (its expansion starts at `z³`). -/
lemma order_three_le_wIter (n : ℕ) : (3 : ℕ∞) ≤ (W.wIter n).order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [wIter_succ, wOp]
    have hX3 : (3 : ℕ∞) ≤ ((X : R⟦X⟧) ^ 3).order :=
      nat_le_order _ 3 (fun i hi => by simp only [coeff_X_pow]; rw [ite_eq_right (by omega)])
    refine order_add₄_ge hX3 ?_ ?_ ?_
    · -- (a₁z + a₂z²) · wₙ
      exact le_order_mul_right ih
    · -- (a₃ + a₄z) · wₙ²
      have h2 : (W.wIter n) ^ 2 = W.wIter n * W.wIter n := by ring
      rw [h2]
      exact le_order_mul_right (le_order_mul_right ih)
    · -- a₆ · wₙ³
      have h3 : (W.wIter n) ^ 3 = W.wIter n * W.wIter n * W.wIter n := by ring
      rw [h3]
      exact le_order_mul_right (le_order_mul_right ih)

private lemma one_le_order_wIter (n : ℕ) : (1 : ℕ∞) ≤ (W.wIter n).order :=
  le_trans (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)) (W.order_three_le_wIter n)

/-- The iteration is `z`-adically Cauchy: `wₙ` and `wₙ₊₁` agree up to order `n`. This is the
contraction property, iterated from `w₀ = 0`. -/
lemma order_wIter_sub_succ (n : ℕ) : (n : ℕ∞) ≤ (W.wIter n - W.wIter (n + 1)).order := by
  induction n with
  | zero => exact zero_le
  | succ n ih =>
    have key := W.order_wOp_sub (W.wIter n) (W.wIter (n + 1))
      (W.one_le_order_wIter n) (W.one_le_order_wIter (n + 1)) ih
    rw [Nat.cast_succ]
    exact key

/-- The coefficients of the iterates stabilise: for `k ≥ n + 1`, the `n`-th coefficient of `wₖ`
no longer changes. -/
lemma coeff_wIter_stable {n k : ℕ} (hk : n + 1 ≤ k) :
    coeff n (W.wIter k) = coeff n (W.wIter (n + 1)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge (n + 1) (k + 1) with h | h
    · have hnk : n + 1 ≤ k := by omega
      have hlt : (n : ℕ∞) < (W.wIter k - W.wIter (k + 1)).order :=
        lt_of_lt_of_le (by exact_mod_cast (show n < k by omega)) (W.order_wIter_sub_succ k)
      have hz : coeff n (W.wIter k - W.wIter (k + 1)) = 0 := coeff_of_lt_order n hlt
      rw [map_sub, sub_eq_zero] at hz
      rw [← hz]; exact ih hnk
    · have hkn : k = n := by omega
      subst hkn; rfl

/-- The Weierstrass expansion `w(z) ∈ R⟦z⟧`, the unique power series of order `≥ 3` solving the
functional equation `w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³`. It is realised as the
`z`-adic limit of the iterates `wₙ`. -/
noncomputable def formalW (W : WeierstrassCurve R) : R⟦X⟧ :=
  PowerSeries.mk fun n => coeff n (W.wIter (n + 1))

lemma coeff_formalW (n : ℕ) : coeff n W.formalW = coeff n (W.wIter (n + 1)) := by
  rw [formalW, coeff_mk]

/-- The `n`-th coefficient of `w` agrees with that of every sufficiently advanced iterate. -/
lemma coeff_formalW_eq_wIter {n k : ℕ} (hk : n + 1 ≤ k) :
    coeff n W.formalW = coeff n (W.wIter k) := by
  rw [coeff_formalW, ← W.coeff_wIter_stable hk]

/-- The expansion has order at least `3`: `w = c₃ z³ + …`. -/
lemma order_formalW : (3 : ℕ∞) ≤ W.formalW.order := by
  refine nat_le_order _ 3 (fun i hi => ?_)
  rw [coeff_formalW]
  exact coeff_of_lt_order i
    (lt_of_lt_of_le (by exact_mod_cast hi) (W.order_three_le_wIter (i + 1)))

private lemma one_le_order_formalW : (1 : ℕ∞) ≤ W.formalW.order :=
  le_trans (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)) W.order_formalW

/-- **The Weierstrass functional equation.** The expansion `w` is a fixed point of the operator
`T`, i.e. `w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³`. -/
theorem formalW_eq : W.formalW = W.wOp W.formalW := by
  ext n
  have hm : (n : ℕ∞) ≤ (W.formalW - W.wIter n).order := by
    refine nat_le_order _ n (fun i hi => ?_)
    rw [map_sub, sub_eq_zero, coeff_formalW, W.coeff_wIter_stable (show i + 1 ≤ n by omega)]
  have key := W.order_wOp_sub W.formalW (W.wIter n) W.one_le_order_formalW
    (W.one_le_order_wIter n) hm
  have key' : ((n + 1 : ℕ) : ℕ∞) ≤ (W.wOp W.formalW - W.wOp (W.wIter n)).order := by
    rw [Nat.cast_succ]; exact key
  have hz : coeff n (W.wOp W.formalW - W.wOp (W.wIter n)) = 0 :=
    coeff_of_lt_order n (lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self n)) key')
  rw [map_sub, sub_eq_zero] at hz
  rw [hz, ← wIter_succ, coeff_formalW]

/-- **Uniqueness of the Weierstrass expansion.** `formalW` is the *unique* power series of
positive order fixed by the operator `T` (`wOp`): any `u` with `1 ≤ u.order` and `u = T u`
equals `W.formalW`. Together with `formalW_eq` and `order_formalW` this characterises `formalW`
as the unique order-`≥ 1` solution of the Weierstrass functional equation. -/
theorem eq_formalW_of_wOp_fixed {u : R⟦X⟧} (hu : 1 ≤ u.order) (hfix : u = W.wOp u) :
    u = W.formalW := by
  -- `u` and `formalW` agree to every finite order, so their difference is `0`.
  have key : ∀ m : ℕ, (m : ℕ∞) ≤ (u - W.formalW).order := by
    intro m
    induction m with
    | zero => exact_mod_cast zero_le
    | succ k ih =>
      have h := W.order_wOp_sub u W.formalW hu W.one_le_order_formalW ih
      rw [← hfix, ← W.formalW_eq] at h
      rw [Nat.cast_succ]
      exact h
  refine sub_eq_zero.mp (PowerSeries.ext fun n => ?_)
  rw [map_zero]
  exact coeff_of_lt_order n
    (lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self n)) (key (n + 1)))

/-- The explicit form of `eq_formalW_of_wOp_fixed`: any positive-order power series `u` solving the
Weierstrass functional equation `u = z³ + (a₁z + a₂z²)u + (a₃ + a₄z)u² + a₆u³` equals `formalW`. -/
theorem eq_formalW_of_functional_eq {u : R⟦X⟧} (hu : 1 ≤ u.order)
    (hfix : u = X ^ 3 + (C W.a₁ * X + C W.a₂ * X ^ 2) * u + (C W.a₃ + C W.a₄ * X) * u ^ 2
      + C W.a₆ * u ^ 3) : u = W.formalW :=
  W.eq_formalW_of_wOp_fixed hu (by rw [wOp]; exact hfix)

/-- If the sum of two orders exceeds `n`, the `n`-th coefficient of the product vanishes. -/
private lemma coeff_mul_eq_zero_of_lt {a b : R⟦X⟧} {n : ℕ}
    (h : (n : ℕ∞) < a.order + b.order) : coeff n (a * b) = 0 :=
  coeff_of_lt_order n (lt_of_lt_of_le h (le_order_mul a b))

/-- The leading coefficient of the expansion is `1`: `w = z³ + a₁z⁴ + …`. Combined with
`order_formalW`, this shows `w` has order exactly `3`. -/
theorem coeff_formalW_three : coeff 3 W.formalW = 1 := by
  have hP1 : coeff 3 ((C W.a₁ * X + C W.a₂ * X ^ 2) * W.formalW) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (3 : ℕ) < 1 + 3))
      (add_le_add W.one_le_order_P₁ W.order_formalW))
  have hP2 : coeff 3 ((C W.a₃ + C W.a₄ * X) * (W.formalW * W.formalW)) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (3 : ℕ) < 0 + (3 + 3)))
      (add_le_add zero_le
        (le_trans (add_le_add W.order_formalW W.order_formalW) (le_order_mul _ _))))
  have hP3 : coeff 3 (C W.a₆ * (W.formalW * W.formalW * W.formalW)) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (3 : ℕ) < 0 + ((3 + 3) + 3)))
      (add_le_add zero_le
        (le_trans (add_le_add (le_trans (add_le_add W.order_formalW W.order_formalW)
          (le_order_mul _ _)) W.order_formalW) (le_order_mul _ _))))
  have hX : coeff 3 ((X : R⟦X⟧) ^ 3) = 1 := by rw [coeff_X_pow]; simp
  rw [formalW_eq, wOp,
    show W.formalW ^ 2 = W.formalW * W.formalW from by ring,
    show W.formalW ^ 3 = W.formalW * W.formalW * W.formalW from by ring]
  simp only [map_add]
  rw [hX, hP1, hP2, hP3]
  ring

/-- Coefficients below the order-`3` vanish: `coeff n w = 0` for `n < 3`. -/
private lemma coeff_formalW_of_lt {n : ℕ} (hn : n < 3) : coeff n W.formalW = 0 :=
  coeff_of_lt_order n (lt_of_lt_of_le (by exact_mod_cast hn) W.order_formalW)

/-- The coefficient of `z⁴` in the expansion is `a₁`: `w = z³ + a₁z⁴ + …`. -/
theorem coeff_formalW_four : coeff 4 W.formalW = W.a₁ := by
  have hXw : coeff 4 (X * W.formalW) = coeff 3 W.formalW := coeff_succ_X_mul 3 W.formalW
  have hX2w : coeff 4 (X ^ 2 * W.formalW) = coeff 2 W.formalW := by
    rw [coeff_X_pow_mul']; norm_num
  have hlin : coeff 4 ((C W.a₁ * X + C W.a₂ * X ^ 2) * W.formalW) = W.a₁ := by
    rw [add_mul, map_add, mul_assoc, coeff_C_mul, hXw, coeff_formalW_three, mul_one,
      mul_assoc, coeff_C_mul, hX2w, W.coeff_formalW_of_lt (by norm_num), mul_zero, add_zero]
  have hP2 : coeff 4 ((C W.a₃ + C W.a₄ * X) * (W.formalW * W.formalW)) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (4 : ℕ) < 0 + (3 + 3)))
      (add_le_add zero_le
        (le_trans (add_le_add W.order_formalW W.order_formalW) (le_order_mul _ _))))
  have hP3 : coeff 4 (C W.a₆ * (W.formalW * W.formalW * W.formalW)) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (4 : ℕ) < 0 + ((3 + 3) + 3)))
      (add_le_add zero_le
        (le_trans (add_le_add (le_trans (add_le_add W.order_formalW W.order_formalW)
          (le_order_mul _ _)) W.order_formalW) (le_order_mul _ _))))
  have hX : coeff 4 ((X : R⟦X⟧) ^ 3) = 0 := by rw [coeff_X_pow]; simp
  rw [formalW_eq, wOp,
    show W.formalW ^ 2 = W.formalW * W.formalW from by ring,
    show W.formalW ^ 3 = W.formalW * W.formalW * W.formalW from by ring]
  simp only [map_add]
  rw [hX, hlin, hP2, hP3]
  ring

/-- The coefficient of `z⁵` in the expansion is `a₁² + a₂`: `w = z³ + a₁z⁴ + (a₁² + a₂)z⁵ + …`. -/
theorem coeff_formalW_five : coeff 5 W.formalW = W.a₁ ^ 2 + W.a₂ := by
  have hXw : coeff 5 (X * W.formalW) = coeff 4 W.formalW := coeff_succ_X_mul 4 W.formalW
  have hX2w : coeff 5 (X ^ 2 * W.formalW) = coeff 3 W.formalW := by
    rw [coeff_X_pow_mul']; norm_num
  have hlin : coeff 5 ((C W.a₁ * X + C W.a₂ * X ^ 2) * W.formalW) = W.a₁ ^ 2 + W.a₂ := by
    rw [add_mul, map_add, mul_assoc, coeff_C_mul, hXw, coeff_formalW_four,
      mul_assoc, coeff_C_mul, hX2w, coeff_formalW_three, mul_one]
    ring
  have hP2 : coeff 5 ((C W.a₃ + C W.a₄ * X) * (W.formalW * W.formalW)) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (5 : ℕ) < 0 + (3 + 3)))
      (add_le_add zero_le
        (le_trans (add_le_add W.order_formalW W.order_formalW) (le_order_mul _ _))))
  have hP3 : coeff 5 (C W.a₆ * (W.formalW * W.formalW * W.formalW)) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (5 : ℕ) < 0 + ((3 + 3) + 3)))
      (add_le_add zero_le
        (le_trans (add_le_add (le_trans (add_le_add W.order_formalW W.order_formalW)
          (le_order_mul _ _)) W.order_formalW) (le_order_mul _ _))))
  have hX : coeff 5 ((X : R⟦X⟧) ^ 3) = 0 := by rw [coeff_X_pow]; simp
  rw [formalW_eq, wOp,
    show W.formalW ^ 2 = W.formalW * W.formalW from by ring,
    show W.formalW ^ 3 = W.formalW * W.formalW * W.formalW from by ring]
  simp only [map_add]
  rw [hX, hlin, hP2, hP3]
  ring

/-- The `z⁶`-coefficient of the expansion is `a₁³ + 2a₁a₂ + a₃`. Here the `w²` term first
contributes (its leading term `z⁶` has coefficient `1`), so unlike the lower coefficients this one
is not simply linear in the `aᵢ`. -/
theorem coeff_formalW_six :
    coeff 6 W.formalW = W.a₁ ^ 3 + 2 * W.a₁ * W.a₂ + W.a₃ := by
  have h0 := W.coeff_formalW_of_lt (show (0 : ℕ) < 3 by norm_num)
  have h1 := W.coeff_formalW_of_lt (show (1 : ℕ) < 3 by norm_num)
  have h2 := W.coeff_formalW_of_lt (show (2 : ℕ) < 3 by norm_num)
  -- The `z⁶` coefficient of `w²`: only the `i = 3` term of the convolution survives.
  have hw2_6 : coeff 6 (W.formalW * W.formalW) = 1 := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, h0, h1, h2,
      coeff_formalW_three, zero_mul, mul_zero, zero_add, add_zero, mul_one]
  have hw2_5 : coeff 5 (W.formalW * W.formalW) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (5 : ℕ) < 3 + 3))
      (add_le_add W.order_formalW W.order_formalW))
  have hXw : coeff 6 (X * W.formalW) = coeff 5 W.formalW := coeff_succ_X_mul 5 W.formalW
  have hX2w : coeff 6 (X ^ 2 * W.formalW) = coeff 4 W.formalW := by
    rw [coeff_X_pow_mul']; norm_num
  have hlin : coeff 6 ((C W.a₁ * X + C W.a₂ * X ^ 2) * W.formalW)
      = W.a₁ ^ 3 + 2 * W.a₁ * W.a₂ := by
    rw [add_mul, map_add, mul_assoc, coeff_C_mul, hXw, coeff_formalW_five,
      mul_assoc, coeff_C_mul, hX2w, coeff_formalW_four]
    ring
  have hXw2 : coeff 6 (X * (W.formalW * W.formalW)) = coeff 5 (W.formalW * W.formalW) :=
    coeff_succ_X_mul 5 _
  have hP2 : coeff 6 ((C W.a₃ + C W.a₄ * X) * (W.formalW * W.formalW)) = W.a₃ := by
    rw [add_mul, map_add, coeff_C_mul, hw2_6, mul_one, mul_assoc, coeff_C_mul, hXw2, hw2_5,
      mul_zero, add_zero]
  have hP3 : coeff 6 (C W.a₆ * (W.formalW * W.formalW * W.formalW)) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (6 : ℕ) < 0 + ((3 + 3) + 3)))
      (add_le_add zero_le
        (le_trans (add_le_add (le_trans (add_le_add W.order_formalW W.order_formalW)
          (le_order_mul _ _)) W.order_formalW) (le_order_mul _ _))))
  have hX : coeff 6 ((X : R⟦X⟧) ^ 3) = 0 := by rw [coeff_X_pow]; simp
  rw [formalW_eq, wOp,
    show W.formalW ^ 2 = W.formalW * W.formalW from by ring,
    show W.formalW ^ 3 = W.formalW * W.formalW * W.formalW from by ring]
  simp only [map_add]
  rw [hX, hlin, hP2, hP3]
  ring

end WeierstrassCurve
