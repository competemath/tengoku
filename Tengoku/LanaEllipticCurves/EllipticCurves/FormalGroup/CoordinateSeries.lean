/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.LaurentSeries
import Tengoku.Seed.RingTheory.PowerSeries.Inverse
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.Expansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coordinate Laurent series `x(z)` and `y(z)` of a Weierstrass curve

Building on the Weierstrass expansion `w = W.formalW ∈ R⟦z⟧` constructed in
`EllipticCurves.FormalGroup.Expansion` — the unique order-`3` solution of the functional equation
`w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³` — this file constructs the affine coordinate
series in the local parameter `z = -x/y` near the origin `O` (Silverman, *The Arithmetic of
Elliptic Curves*, IV.1):
$$ x(z) = \frac{z}{w(z)}, \qquad y(z) = \frac{-1}{w(z)}. $$
These have poles at `z = 0` (`x` of order `2`, `y` of order `3`), so they naturally live in the
Laurent series ring `R⸨X⸩`.

The construction is elementary once one observes that `w = z³ · v` where `v` is a *unit* power
series (its constant term is the leading coefficient `1` of `w`). Concretely `v = W.wCofactor`,
and `x(z) = z⁻² · v⁻¹`, `y(z) = -z⁻³ · v⁻¹`, with `v⁻¹ = PowerSeries.invOfUnit v 1`. This avoids
any division in a non-field ring: everything is a product of `HahnSeries.single` monomials with
coercions of honest power series.

## Main definitions

* `WeierstrassCurve.wCofactor` : the unit power series `v` with `w = z³ · v`.
* `WeierstrassCurve.formalX`, `WeierstrassCurve.formalY` : the coordinate Laurent series `x(z)`,
  `y(z) ∈ R⸨X⸩`.

## Main results

* `WeierstrassCurve.formalW_eq_X_pow_mul_wCofactor` : `w = z³ · v`.
* `WeierstrassCurve.isUnit_wCofactor`, `WeierstrassCurve.isUnit_coe_formalW` : `v` and (hence) `w`
  are units (the latter in `R⸨X⸩`).
* `WeierstrassCurve.order_formalW_eq` : `order w = 3` (over a nontrivial ring).
* `WeierstrassCurve.formalX_mul_coe_formalW` : `x(z) · w(z) = z`.
* `WeierstrassCurve.formalY_mul_coe_formalW` : `y(z) · w(z) = -1`.
* `WeierstrassCurve.single_one_mul_formalY` : `z · y(z) = -x(z)`, i.e. `z = -x/y`.
* `WeierstrassCurve.coeff_formalX_neg_two`, `WeierstrassCurve.coeff_formalY_neg_three` : the leading
  (polar) coefficients `1` and `-1`, and `coeff_formalX_of_lt`, `coeff_formalY_of_lt` pin the pole
  orders (`2` and `3`).
* `WeierstrassCurve.formalX_formalY_weierstrass` : the point-on-curve identity, that `(x(z), y(z))`
  satisfies the Weierstrass equation as Laurent series (the reformulation of `formalW_eq`).
* `WeierstrassCurve.coeff_formalX_neg_one` (`= -a₁`), `coeff_formalX_zero` (`= -a₂`),
  `coeff_formalX_one` (`= -a₃`), `coeff_formalY_neg_two` (`= a₁`), `coeff_formalY_neg_one` (`= a₂`),
  `coeff_formalY_zero` (`= a₃`) : the sub-leading coefficients, so
  `x = z⁻² - a₁ z⁻¹ - a₂ - a₃ z - …` and `y = -z⁻³ + a₁ z⁻² + a₂ z⁻¹ + a₃ + …` (Silverman AEC IV.1).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

namespace WeierstrassCurve

open PowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The unit cofactor `v` with `w = z³ · v` -/

/-- The power series `v` obtained by dividing the Weierstrass expansion `w` by `z³`; it satisfies
`w = z³ · v` and has constant term `1`, so it is a unit. -/
noncomputable def wCofactor (W : WeierstrassCurve R) : R⟦X⟧ :=
  PowerSeries.mk fun n => coeff (n + 3) W.formalW

lemma coeff_wCofactor (n : ℕ) : coeff n W.wCofactor = coeff (n + 3) W.formalW := by
  rw [wCofactor, coeff_mk]

/-- The Weierstrass expansion factors as `w = z³ · v` with `v = W.wCofactor`. -/
theorem formalW_eq_X_pow_mul_wCofactor : W.formalW = X ^ 3 * W.wCofactor := by
  ext m
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_wCofactor, Nat.sub_add_cancel h]
  · exact coeff_of_lt_order m
      (lt_of_lt_of_le (by exact_mod_cast Nat.not_le.mp h) W.order_formalW)

/-- The constant term of the cofactor `v` is the leading coefficient `1` of `w`. -/
@[simp]
theorem constantCoeff_wCofactor : constantCoeff W.wCofactor = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_wCofactor, zero_add, coeff_formalW_three]

/-- The cofactor `v` is a unit power series. -/
theorem isUnit_wCofactor : IsUnit W.wCofactor :=
  isUnit_iff_constantCoeff.mpr (by simp)

/-- The cofactor `v` times its chosen `invOfUnit`-inverse `v⁻¹` is `1`. -/
theorem wCofactor_mul_invOfUnit : W.wCofactor * invOfUnit W.wCofactor 1 = 1 :=
  mul_invOfUnit W.wCofactor 1 (by rw [constantCoeff_wCofactor, Units.val_one])

/-- Over a nontrivial ring the expansion has order exactly `3`: `w = z³ + …`. -/
theorem order_formalW_eq [Nontrivial R] : W.formalW.order = 3 :=
  le_antisymm (order_le 3 (by rw [coeff_formalW_three]; exact one_ne_zero)) W.order_formalW

/-! ### The coordinate Laurent series -/

open scoped LaurentSeries

/-- The image of `w` in the Laurent series ring factors as `z³ · v`. -/
theorem coe_formalW_eq :
    (W.formalW : R⸨X⸩) = HahnSeries.single (3 : ℤ) 1 * (W.wCofactor : R⸨X⸩) := by
  rw [W.formalW_eq_X_pow_mul_wCofactor, coe_mul, coe_pow, HahnSeries.ofPowerSeries_X,
    HahnSeries.single_pow]
  norm_num

/-- In the Laurent series ring, `w` is a unit (its leading monomial `z³` and the unit factor `v`
are both invertible). This is the key input to the formal group law. -/
theorem isUnit_coe_formalW : IsUnit (W.formalW : R⸨X⸩) := by
  rw [coe_formalW_eq]
  refine IsUnit.mul ?_ (W.isUnit_wCofactor.map (HahnSeries.ofPowerSeries ℤ R))
  refine ⟨⟨HahnSeries.single (3 : ℤ) 1, HahnSeries.single (-3 : ℤ) 1, ?_, ?_⟩, rfl⟩
  · simp [HahnSeries.single_mul_single]
  · simp [HahnSeries.single_mul_single]

/-- The coordinate series `x(z) = z / w(z) = z⁻² · v⁻¹ ∈ R⸨X⸩`. It has a pole of order `2` at
the origin with leading coefficient `1`. -/
noncomputable def formalX (W : WeierstrassCurve R) : R⸨X⸩ :=
  HahnSeries.single (-2 : ℤ) 1 * ((invOfUnit W.wCofactor 1 : R⟦X⟧) : R⸨X⸩)

/-- The coordinate series `y(z) = -1 / w(z) = -z⁻³ · v⁻¹ ∈ R⸨X⸩`. It has a pole of order `3` at
the origin with leading coefficient `-1`. -/
noncomputable def formalY (W : WeierstrassCurve R) : R⸨X⸩ :=
  HahnSeries.single (-3 : ℤ) (-1) * ((invOfUnit W.wCofactor 1 : R⟦X⟧) : R⸨X⸩)

/-- **Defining identity for `x(z)`:** `x(z) · w(z) = z`. -/
theorem formalX_mul_coe_formalW :
    W.formalX * (W.formalW : R⸨X⸩) = HahnSeries.single (1 : ℤ) 1 := by
  rw [formalX, coe_formalW_eq, mul_mul_mul_comm, HahnSeries.single_mul_single,
    ← coe_mul, mul_comm (invOfUnit W.wCofactor 1) W.wCofactor,
    W.wCofactor_mul_invOfUnit, coe_one, mul_one]
  norm_num

/-- **Defining identity for `y(z)`:** `y(z) · w(z) = -1`. -/
theorem formalY_mul_coe_formalW :
    W.formalY * (W.formalW : R⸨X⸩) = -1 := by
  have hg : ((-3 : ℤ) + 3) = 0 := by norm_num
  have hr : ((-1 : R) * 1) = -(1 : R) := by ring
  rw [formalY, coe_formalW_eq, mul_mul_mul_comm, HahnSeries.single_mul_single,
    ← coe_mul, mul_comm (invOfUnit W.wCofactor 1) W.wCofactor,
    W.wCofactor_mul_invOfUnit, coe_one, mul_one, hg, hr,
    HahnSeries.single_neg, HahnSeries.single_zero_one]

/-- The relation `z · y(z) = -x(z)`, i.e. `z = -x(z)/y(z)`: the local parameter is recovered from
the coordinates. -/
theorem single_one_mul_formalY :
    HahnSeries.single (1 : ℤ) 1 * W.formalY = -W.formalX := by
  have hg : ((1 : ℤ) + -3) = -2 := by norm_num
  have hr : ((1 : R) * -1) = -(1 : R) := by ring
  rw [formalY, formalX, ← mul_assoc, HahnSeries.single_mul_single, hg, hr,
    HahnSeries.single_neg, neg_mul]

/-! ### Leading terms and pole orders -/

/-- Negative-index coefficients of a coerced power series vanish. -/
theorem coe_powerSeries_coeff_of_neg (p : R⟦X⟧) {g : ℤ} (hg : g < 0) :
    (p : R⸨X⸩).coeff g = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  rintro ⟨n, hn⟩
  simp only [Nat.castOrderEmbedding, OrderEmbedding.coe_ofStrictMono] at hn
  omega

/-- The leading coefficient of `x(z)` is `1`, at the pole `z⁻²`. -/
@[simp]
theorem coeff_formalX_neg_two : W.formalX.coeff (-2) = 1 := by
  have h0 : ((-2 : ℤ) - (-2)) = ((0 : ℕ) : ℤ) := by norm_num
  rw [formalX, HahnSeries.coeff_single_mul, h0, LaurentSeries.coeff_coe_powerSeries]
  simp

/-- The leading coefficient of `y(z)` is `-1`, at the pole `z⁻³`. -/
@[simp]
theorem coeff_formalY_neg_three : W.formalY.coeff (-3) = -1 := by
  have h0 : ((-3 : ℤ) - (-3)) = ((0 : ℕ) : ℤ) := by norm_num
  rw [formalY, HahnSeries.coeff_single_mul, h0, LaurentSeries.coeff_coe_powerSeries]
  simp

/-- `x(z)` has a pole of order exactly `2`: coefficients below `z⁻²` vanish. -/
theorem coeff_formalX_of_lt {g : ℤ} (hg : g < -2) : W.formalX.coeff g = 0 := by
  rw [formalX, HahnSeries.coeff_single_mul, one_mul]
  exact coe_powerSeries_coeff_of_neg _ (by omega)

/-- `y(z)` has a pole of order exactly `3`: coefficients below `z⁻³` vanish. -/
theorem coeff_formalY_of_lt {g : ℤ} (hg : g < -3) : W.formalY.coeff g = 0 := by
  rw [formalY, HahnSeries.coeff_single_mul, coe_powerSeries_coeff_of_neg _ (by omega), mul_zero]

/-! ### The point-on-curve identity -/

/-- The Weierstrass functional equation `formalW_eq`, transported into the Laurent series ring and
written with the constants `HahnSeries.C W.aᵢ` and the local parameter `z = single 1 1`. -/
theorem coe_formalW_functional_eq :
    (W.formalW : R⸨X⸩)
      = HahnSeries.single (1 : ℤ) 1 ^ 3
        + (HahnSeries.C W.a₁ * HahnSeries.single 1 1
            + HahnSeries.C W.a₂ * HahnSeries.single 1 1 ^ 2) * (W.formalW : R⸨X⸩)
        + (HahnSeries.C W.a₃ + HahnSeries.C W.a₄ * HahnSeries.single 1 1)
            * (W.formalW : R⸨X⸩) ^ 2
        + HahnSeries.C W.a₆ * (W.formalW : R⸨X⸩) ^ 3 := by
  conv_lhs => rw [W.formalW_eq, wOp]
  simp only [PowerSeries.coe_add, PowerSeries.coe_mul, PowerSeries.coe_pow, PowerSeries.coe_C,
    PowerSeries.coe_X]

/-- **The point-on-curve identity.** The coordinate Laurent series `(x(z), y(z))` satisfy the
Weierstrass equation of `W`:
`y² + a₁·x·y + a₃·y = x³ + a₂·x² + a₄·x + a₆` in `R⸨X⸩`.
This certifies the parametrisation `x = z/w`, `y = -1/w` of the curve near the origin `O`; it is the
algebraic reformulation of the functional equation `formalW_eq` cleared of the unit `w³`. -/
theorem formalX_formalY_weierstrass :
    W.formalY ^ 2 + HahnSeries.C W.a₁ * W.formalX * W.formalY + HahnSeries.C W.a₃ * W.formalY
      = W.formalX ^ 3 + HahnSeries.C W.a₂ * W.formalX ^ 2 + HahnSeries.C W.a₄ * W.formalX
        + HahnSeries.C W.a₆ := by
  set w : R⸨X⸩ := (W.formalW : R⸨X⸩) with hw
  set z : R⸨X⸩ := HahnSeries.single (1 : ℤ) 1 with hz
  have hx : W.formalX * w = z := W.formalX_mul_coe_formalW
  have hy : W.formalY * w = -1 := W.formalY_mul_coe_formalW
  have hFE : w = z ^ 3
      + (HahnSeries.C W.a₁ * z + HahnSeries.C W.a₂ * z ^ 2) * w
      + (HahnSeries.C W.a₃ + HahnSeries.C W.a₄ * z) * w ^ 2
      + HahnSeries.C W.a₆ * w ^ 3 := W.coe_formalW_functional_eq
  -- It suffices to prove the identity after multiplying by the unit `w³`.
  refine (((W.isUnit_coe_formalW.pow 3)).mul_left_inj).mp ?_
  -- The cleared identity reduces each monomial via `hx`, `hy` and finally to `hFE`.
  have e1 : W.formalY ^ 2 * w ^ 3 = w := by
    linear_combination (w * (W.formalY * w - 1)) * hy
  have e2 : W.formalX * W.formalY * w ^ 3 = -(z * w) := by
    linear_combination (W.formalY * w ^ 2) * hx + (z * w) * hy
  have e3 : W.formalY * w ^ 3 = -w ^ 2 := by
    linear_combination (w ^ 2) * hy
  have e4 : W.formalX ^ 3 * w ^ 3 = z ^ 3 := by
    linear_combination ((W.formalX * w) ^ 2 + (W.formalX * w) * z + z ^ 2) * hx
  have e5 : W.formalX ^ 2 * w ^ 3 = z ^ 2 * w := by
    linear_combination (w * (W.formalX * w + z)) * hx
  have e6 : W.formalX * w ^ 3 = z * w ^ 2 := by
    linear_combination (w ^ 2) * hx
  linear_combination e1 + HahnSeries.C W.a₁ * e2 + HahnSeries.C W.a₃ * e3 - e4
    - HahnSeries.C W.a₂ * e5 - HahnSeries.C W.a₄ * e6 + hFE

/-! ### Sub-leading coefficients -/

private lemma coeff_wCofactor_zero : coeff 0 W.wCofactor = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_wCofactor]

private lemma coeff_wCofactor_one : coeff 1 W.wCofactor = W.a₁ := by
  rw [coeff_wCofactor]; exact W.coeff_formalW_four

private lemma coeff_wCofactor_two : coeff 2 W.wCofactor = W.a₁ ^ 2 + W.a₂ := by
  rw [coeff_wCofactor]; exact W.coeff_formalW_five

private lemma coeff_wCofactor_three :
    coeff 3 W.wCofactor = W.a₁ ^ 3 + 2 * W.a₁ * W.a₂ + W.a₃ := by
  rw [coeff_wCofactor]; exact W.coeff_formalW_six

private lemma coeff_invOfUnit_wCofactor_zero :
    coeff 0 (invOfUnit W.wCofactor 1) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_invOfUnit]; simp

/-- The `z¹`-coefficient of the inverse cofactor `v⁻¹` is `-a₁`. -/
theorem coeff_invOfUnit_wCofactor_one :
    coeff 1 (invOfUnit W.wCofactor 1) = -W.a₁ := by
  have h := congrArg (coeff 1) W.wCofactor_mul_invOfUnit
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
    coeff_wCofactor_zero, coeff_wCofactor_one, coeff_invOfUnit_wCofactor_zero, coeff_one,
    one_mul, mul_one, one_ne_zero, ite_false] at h
  linear_combination h

/-- The `z²`-coefficient of the inverse cofactor `v⁻¹` is `-a₂`. -/
theorem coeff_invOfUnit_wCofactor_two :
    coeff 2 (invOfUnit W.wCofactor 1) = -W.a₂ := by
  have h := congrArg (coeff 2) W.wCofactor_mul_invOfUnit
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
    Nat.reduceSub, coeff_wCofactor_zero, coeff_wCofactor_one, coeff_wCofactor_two,
    coeff_invOfUnit_wCofactor_zero, coeff_invOfUnit_wCofactor_one, coeff_one,
    one_mul, mul_one, ite_false, OfNat.ofNat_ne_zero] at h
  linear_combination h

/-- The `z³`-coefficient of the inverse cofactor `v⁻¹` is `-a₃` (the higher terms of `v` cancel). -/
theorem coeff_invOfUnit_wCofactor_three :
    coeff 3 (invOfUnit W.wCofactor 1) = -W.a₃ := by
  have h := congrArg (coeff 3) W.wCofactor_mul_invOfUnit
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
    Nat.reduceSub, coeff_wCofactor_zero, coeff_wCofactor_one, coeff_wCofactor_two,
    coeff_wCofactor_three, coeff_invOfUnit_wCofactor_zero, coeff_invOfUnit_wCofactor_one,
    coeff_invOfUnit_wCofactor_two, coeff_one, one_mul, mul_one, ite_false,
    OfNat.ofNat_ne_zero] at h
  linear_combination h

/-- The sub-leading coefficient of `x(z)`: `coeff (-1) x = -a₁`, so `x = z⁻² - a₁ z⁻¹ - …`. -/
@[simp]
theorem coeff_formalX_neg_one : W.formalX.coeff (-1) = -W.a₁ := by
  have h0 : ((-1 : ℤ) - (-2)) = ((1 : ℕ) : ℤ) := by norm_num
  rw [formalX, HahnSeries.coeff_single_mul, h0, LaurentSeries.coeff_coe_powerSeries,
    coeff_invOfUnit_wCofactor_one, one_mul]

/-- The constant coefficient of `x(z)`: `coeff 0 x = -a₂`. -/
@[simp]
theorem coeff_formalX_zero : W.formalX.coeff 0 = -W.a₂ := by
  have h0 : ((0 : ℤ) - (-2)) = ((2 : ℕ) : ℤ) := by norm_num
  rw [formalX, HahnSeries.coeff_single_mul, h0, LaurentSeries.coeff_coe_powerSeries,
    coeff_invOfUnit_wCofactor_two, one_mul]

/-- The `z¹`-coefficient of `x(z)`: `coeff 1 x = -a₃`, so `x = z⁻² - a₁ z⁻¹ - a₂ - a₃ z - …`. -/
@[simp]
theorem coeff_formalX_one : W.formalX.coeff 1 = -W.a₃ := by
  have h0 : ((1 : ℤ) - (-2)) = ((3 : ℕ) : ℤ) := by norm_num
  rw [formalX, HahnSeries.coeff_single_mul, h0, LaurentSeries.coeff_coe_powerSeries,
    coeff_invOfUnit_wCofactor_three, one_mul]

/-- The sub-leading coefficient of `y(z)`: `coeff (-2) y = a₁`, so `y = -z⁻³ + a₁ z⁻² + …`. -/
@[simp]
theorem coeff_formalY_neg_two : W.formalY.coeff (-2) = W.a₁ := by
  have h0 : ((-2 : ℤ) - (-3)) = ((1 : ℕ) : ℤ) := by norm_num
  rw [formalY, HahnSeries.coeff_single_mul, h0, LaurentSeries.coeff_coe_powerSeries,
    coeff_invOfUnit_wCofactor_one]
  ring

/-- The `z⁻¹`-coefficient of `y(z)`: `coeff (-1) y = a₂`, so `y = -z⁻³ + a₁ z⁻² + a₂ z⁻¹ + …`. -/
@[simp]
theorem coeff_formalY_neg_one : W.formalY.coeff (-1) = W.a₂ := by
  have h0 : ((-1 : ℤ) - (-3)) = ((2 : ℕ) : ℤ) := by norm_num
  rw [formalY, HahnSeries.coeff_single_mul, h0, LaurentSeries.coeff_coe_powerSeries,
    coeff_invOfUnit_wCofactor_two]
  ring

/-- The constant coefficient of `y(z)`: `coeff 0 y = a₃`, so
`y = -z⁻³ + a₁ z⁻² + a₂ z⁻¹ + a₃ + …`. -/
@[simp]
theorem coeff_formalY_zero : W.formalY.coeff 0 = W.a₃ := by
  have h0 : ((0 : ℤ) - (-3)) = ((3 : ℕ) : ℤ) := by norm_num
  rw [formalY, HahnSeries.coeff_single_mul, h0, LaurentSeries.coeff_coe_powerSeries,
    coeff_invOfUnit_wCofactor_three]
  ring

end WeierstrassCurve
