/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Jacobian.Basic

/-!
# Negation and addition formulae for nonsingular points in Jacobian coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular Jacobian points on `W` can be given
negation and addition operations defined by an analogue of the secant-and-tangent process in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`, but the polynomials involved are
`(2, 3, 1)`-homogeneous, so any instances of division become multiplication in the `Z`-coordinate.
Most computational proofs are immediate from their analogous proofs for affine coordinates.

This file defines polynomials associated to negation, doubling, and addition of Jacobian point
representatives. The group operations and the group law on actual nonsingular Jacobian points will
be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`.

## Main definitions

* `WeierstrassCurve.Jacobian.negY`: the `Y`-coordinate of `-P`.
* `WeierstrassCurve.Jacobian.dblZ`: the `Z`-coordinate of `2 • P`.
* `WeierstrassCurve.Jacobian.dblX`: the `X`-coordinate of `2 • P`.
* `WeierstrassCurve.Jacobian.negDblY`: the `Y`-coordinate of `-(2 • P)`.
* `WeierstrassCurve.Jacobian.dblY`: the `Y`-coordinate of `2 • P`.
* `WeierstrassCurve.Jacobian.addZ`: the `Z`-coordinate of `P + Q`.
* `WeierstrassCurve.Jacobian.addX`: the `X`-coordinate of `P + Q`.
* `WeierstrassCurve.Jacobian.negAddY`: the `Y`-coordinate of `-(P + Q)`.
* `WeierstrassCurve.Jacobian.addY`: the `Y`-coordinate of `P + Q`.

## Implementation notes

The definitions of `WeierstrassCurve.Jacobian.addX` and `WeierstrassCurve.Jacobian.negAddY` are
given explicitly by large polynomials that are homogeneous of degrees `8` and `12` respectively.
Clearing the denominators of their corresponding affine rational functions in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` would give polynomials that are
homogeneous of degrees `12` and `18` respectively, so their actual definitions are off by powers of
a certain polynomial factor that is homogeneous of degree `2`. This factor divides their
corresponding affine polynomials only modulo the `(2, 3, 1)`-homogeneous Weierstrass equation, so
their large quotient polynomials are calculated explicitly in a computer algebra system. All of this
is done to ensure that the definitions of both `WeierstrassCurve.Jacobian.dblXYZ` and
`WeierstrassCurve.Jacobian.addXYZ` are `(2, 3, 1)`-homogeneous of degree `4`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, negation, doubling, addition, group law
-/

@[expose] public section

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Jacobian R} {W : Jacobian F}

namespace Jacobian

/-! ## Negation formulae in Jacobian coordinates -/

variable (W') in
/-- The `Y`-coordinate of a representative of `-P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
def negY (P : Fin 3 → R) : R :=
  -P y - W'.a₁ * P x * P z - W'.a₃ * P z ^ 3

/--
@isnad1 id=eq.0h5v.s7.83286f1963f4 from=seed src=0 shape=74b7946d vocab=21c518a1
-/
lemma negY_eq (X Y Z : R) : W'.negY ![X, Y, Z] = -Y - W'.a₁ * X * Z - W'.a₃ * Z ^ 3 :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.6db2518f8ebb from=seed src=0 shape=94adfe35 vocab=c1e4b47d
-/
lemma negY_smul (P : Fin 3 → R) (u : R) : W'.negY (u • P) = u ^ 3 * W'.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.1h3v.s6.14dd1a0a583c from=seed src=0 shape=f142adff vocab=84262d7b
-/
lemma negY_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.negY P = -P y := by
  rw [negY, hPz, mul_zero, sub_zero, zero_pow three_ne_zero, mul_zero, sub_zero]

/--
@isnad1 id=eq.1h3v.s8.09ca0fd035e2 from=seed src=0 shape=9a7eb228 vocab=2abb60b1
-/
lemma negY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negY P / P z ^ 3 = W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [negY, Affine.negY]; ring1))
    -W.a₁ * P x / P z ^ 2 * div_self hPz - W.a₃ * div_self (pow_ne_zero 3 hPz)

/--
@isnad1 id=eq.3h4v.s9.c28bf34df5aa from=seed src=0 shape=f701f00d vocab=b292cb1d
-/
lemma Y_sub_Y_mul_Y_sub_negY {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (P y * Q z ^ 3 - W'.negY Q * P z ^ 3) = 0 := by
  linear_combination (norm := (rw [negY]; ring1)) Q z ^ 6 * (equation_iff P).mp hP
    - P z ^ 6 * (equation_iff Q).mp hQ + (P x ^ 2 * Q z ^ 4 + P x * Q x * P z ^ 2 * Q z ^ 2
      + Q x ^ 2 * P z ^ 4 - W'.a₁ * P y * P z * Q z ^ 4 + W'.a₂ * P x * P z ^ 2 * Q z ^ 4
      + W'.a₂ * Q x * P z ^ 4 * Q z ^ 2 + W'.a₄ * P z ^ 4 * Q z ^ 4) * hx

/--
@isnad1 id=eq.4h4v.s8.62d9156584c2 from=seed src=0 shape=61bc9828 vocab=c2d514ce
-/
lemma Y_eq_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    P y * Q z ^ 3 = W'.negY Q * P z ^ 3 :=
  sub_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <|
    sub_ne_zero.mpr hy

/--
@isnad1 id=eq.4h4v.s8.752403a84e19 from=seed src=0 shape=cd4756e2 vocab=c2d514ce
-/
lemma Y_eq_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W'.negY Q * P z ^ 3) :
    P y * Q z ^ 3 = Q y * P z ^ 3 :=
  sub_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_right <|
    sub_ne_zero.mpr hy

/--
@isnad1 id=iff.2h4v.s8.50a4b7ead26a from=seed src=0 shape=701fc700 vocab=794f20b1
-/
lemma Y_eq_iff' {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z ^ 3 = W.negY Q * P z ^ 3 ↔
      P y / P z ^ 3 = W.toAffine.negY (Q x / Q z ^ 2) (Q y / Q z ^ 3) :=
  negY_of_Z_ne_zero hQz ▸ (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)).symm

/--
@isnad1 id=eq.1h4v.s9.462f78e8686e from=seed src=0 shape=d567b74c vocab=f248fc90
-/
lemma Y_sub_Y_add_Y_sub_negY {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) + (P y * Q z ^ 3 - W'.negY Q * P z ^ 3) =
      (P y - W'.negY P) * Q z ^ 3 := by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * P z * Q z * hx

/--
@isnad1 id=ne.4h4v.s8.f4514806bb7d from=seed src=0 shape=d50ae2bb vocab=c2d514ce
-/
lemma Y_ne_negY_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    P y ≠ W'.negY P := by
  have hy' : P y * Q z ^ 3 - W'.negY Q * P z ^ 3 = 0 :=
    (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <| sub_ne_zero_of_ne hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z ^ 3 * hy - hy'

/--
@isnad1 id=ne.4h4v.s8.4334dcc42ea7 from=seed src=0 shape=16393969 vocab=c2d514ce
-/
lemma Y_ne_negY_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ W'.negY Q * P z ^ 3) : P y ≠ W'.negY P := by
  have hy' : P y * Q z ^ 3 - Q y * P z ^ 3 = 0 :=
    (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_right <| sub_ne_zero_of_ne hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z ^ 3 * hy - hy'

/--
@isnad1 id=eq.4h4v.s9.1b2d76a015ac from=seed src=0 shape=4d7166a2 vocab=ef5d6c83
-/
lemma Y_eq_negY_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : P y = W'.negY P :=
  mul_left_injective₀ (pow_ne_zero 3 hQz) <| by
    linear_combination (norm := ring1) -Y_sub_Y_add_Y_sub_negY hx + hy + hy'

/--
@isnad1 id=iff.2h3v.s8.9e6de9151892 from=seed src=0 shape=074e78d0 vocab=51f9e711
-/
lemma nonsingular_iff_of_Y_eq_negY {P : Fin 3 → F} (hPz : P z ≠ 0) (hy : P y = W.negY P) :
    W.Nonsingular P ↔ W.Equation P ∧ eval P W.polynomialX ≠ 0 := by
  have hy' : eval P W.polynomialY = P y - W.negY P := by rw [negY, eval_polynomialY]; ring1
  rw [nonsingular_iff_of_Z_ne_zero hPz, hy', hy, sub_self, ne_self_iff_false, or_false]

/-! ## Doubling formulae in Jacobian coordinates -/

variable (W') in
/-- The unit associated to a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve `W` that is `2`-torsion.

More specifically, the unit `u` such that `W.add P P = u • ![1, 1, 0]` where `P = W.neg P`. -/
noncomputable def dblU (P : Fin 3 → R) : R :=
  eval P W'.polynomialX

/--
@isnad1 id=eq.0h3v.s8.10eae6c8efb5 from=seed src=0 shape=b482f983 vocab=e28228f9
-/
lemma dblU_eq (P : Fin 3 → R) : W'.dblU P =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) := by
  rw [dblU, eval_polynomialX]

/--
@isnad1 id=eq.0h4v.s6.7b1674b2210c from=seed src=0 shape=94adfe35 vocab=19a530b7
-/
lemma dblU_smul (P : Fin 3 → R) (u : R) : W'.dblU (u • P) = u ^ 4 * W'.dblU P := by
  simp only [dblU_eq, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.1h3v.s7.5fa19b7641f1 from=seed src=0 shape=0a518726 vocab=2b449bfc
-/
lemma dblU_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.dblU P = -3 * P x ^ 2 := by
  rw [dblU_eq, hPz]
  ring1

/--
@isnad1 id=ne.6h4v.s9.b531beedd3fc from=seed src=0 shape=50a66502 vocab=f58177d9
-/
lemma dblU_ne_zero_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.dblU P ≠ 0 :=
  ((nonsingular_iff_of_Y_eq_negY hPz <| Y_eq_negY_of_Y_eq hQz hx hy hy').mp hP).right

/--
@isnad1 id=isunit.6h4v.s9.987312fd241f from=seed src=0 shape=45823a5e vocab=36983f1e
-/
lemma isUnit_dblU_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : IsUnit (W.dblU P) :=
  (dblU_ne_zero_of_Y_eq hP hPz hQz hx hy hy').isUnit

variable (W') in
/-- The `Z`-coordinate of a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
def dblZ (P : Fin 3 → R) : R :=
  P z * (P y - W'.negY P)

/--
@isnad1 id=eq.0h4v.s6.ae262cae006e from=seed src=0 shape=94adfe35 vocab=5531c28e
-/
lemma dblZ_smul (P : Fin 3 → R) (u : R) : W'.dblZ (u • P) = u ^ 4 * W'.dblZ P := by
  simp only [dblZ, negY_smul, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.1h3v.s6.b097665a5726 from=seed src=0 shape=55d59f0b vocab=2d15f0cc
-/
lemma dblZ_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.dblZ P = 0 := by
  rw [dblZ, hPz, zero_mul]

/--
@isnad1 id=eq.4h4v.s9.1367fdc19ebb from=seed src=0 shape=f84615b4 vocab=c876f7b8
-/
lemma dblZ_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : W'.dblZ P = 0 := by
  rw [dblZ, Y_eq_negY_of_Y_eq hQz hx hy hy', sub_self, mul_zero]

/--
@isnad1 id=ne.5h4v.s8.3d59781f2fe1 from=seed src=0 shape=912535f2 vocab=b15ade35
-/
lemma dblZ_ne_zero_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : W'.dblZ P ≠ 0 :=
  mul_ne_zero hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne hP hQ hx hy

/--
@isnad1 id=isunit.5h4v.s8.cb7778c3b230 from=seed src=0 shape=7177a242 vocab=133e14e5
-/
lemma isUnit_dblZ_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : IsUnit (W.dblZ P) :=
  (dblZ_ne_zero_of_Y_ne hP hQ hPz hx hy).isUnit

/--
@isnad1 id=ne.5h4v.s8.6338a1006861 from=seed src=0 shape=e71e5c2f vocab=9cb3e28e
-/
lemma dblZ_ne_zero_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ W'.negY Q * P z ^ 3) : W'.dblZ P ≠ 0 :=
  mul_ne_zero hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hx hy

/--
@isnad1 id=isunit.5h4v.s8.da03a72b5f23 from=seed src=0 shape=969cc982 vocab=aea0d1f1
-/
lemma isUnit_dblZ_of_Y_ne' {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    IsUnit (W.dblZ P) :=
  (dblZ_ne_zero_of_Y_ne' hP hQ hPz hx hy).isUnit

private lemma toAffine_slope_of_eq [DecidableEq F] {P Q : Fin 3 → F}
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3) =
      -W.dblU P / W.dblZ P := by
  simp only [X_eq_iff hPz hQz, ne_eq, Y_eq_iff' hPz hQz] at hx hy
  rw [Affine.slope_of_Y_ne hx <| negY_of_Z_ne_zero hQz ▸ hy, ← negY_of_Z_ne_zero hPz, dblU_eq, dblZ]
  simp [field]

variable (W') in
/-- The `X`-coordinate of a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
noncomputable def dblX (P : Fin 3 → R) : R :=
  W'.dblU P ^ 2 - W'.a₁ * W'.dblU P * P z * (P y - W'.negY P)
    - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * (P y - W'.negY P) ^ 2

/--
@isnad1 id=eq.0h4v.s6.56782a96e54f from=seed src=0 shape=1e54a7e6 vocab=4ad31fb0
-/
lemma dblX_smul (P : Fin 3 → R) (u : R) : W'.dblX (u • P) = (u ^ 4) ^ 2 * W'.dblX P := by
  simp only [dblX, dblU_smul, negY_smul, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.2h3v.s7.9653d51af448 from=seed src=0 shape=c2440c15 vocab=b4e984b8
-/
lemma dblX_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblX P = (P x ^ 2) ^ 2 := by
  linear_combination (norm := (rw [dblX, dblU_of_Z_eq_zero hPz, negY_of_Z_eq_zero hPz, hPz]; ring1))
    -8 * P x * (equation_of_Z_eq_zero hPz).mp hP

/--
@isnad1 id=eq.4h4v.s9.e752bc5ccbfd from=seed src=0 shape=c6b0e566 vocab=9a5eb05a
-/
lemma dblX_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : W'.dblX P = W'.dblU P ^ 2 := by
  rw [dblX, Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

private lemma toAffine_addX_of_eq {P : Fin 3 → F} (hPz : P z ≠ 0) {n d : F} (hd : d ≠ 0) :
    W.toAffine.addX (P x / P z ^ 2) (P x / P z ^ 2) (-n / (P z * d)) =
      (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * d ^ 2) / (P z * d) ^ 2 := by
  simp [field]
  ring1

/--
@isnad1 id=eq.6h4v.s9.f395609cb14e from=seed src=0 shape=8ac52b44 vocab=7f78cfab
-/
lemma dblX_of_Z_ne_zero [DecidableEq F]
    {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.dblX P / W.dblZ P ^ 2 = W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [dblX, toAffine_slope_of_eq hPz hQz hx hy, dblZ, ← (X_eq_iff hPz hQz).mp hx,
    toAffine_addX_of_eq hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hx hy]

variable (W') in
/-- The `Y`-coordinate of a representative of `-(2 • P)` for a Jacobian point representative `P` on
a Weierstrass curve. -/
noncomputable def negDblY (P : Fin 3 → R) : R :=
  -W'.dblU P * (W'.dblX P - P x * (P y - W'.negY P) ^ 2) + P y * (P y - W'.negY P) ^ 3

/--
@isnad1 id=eq.0h4v.s6.fd896ddabcd4 from=seed src=0 shape=1e54a7e6 vocab=10e5fdf4
-/
lemma negDblY_smul (P : Fin 3 → R) (u : R) : W'.negDblY (u • P) = (u ^ 4) ^ 3 * W'.negDblY P := by
  simp only [negDblY, dblU_smul, dblX_smul, negY_smul, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.2h3v.s7.453590bb4d82 from=seed src=0 shape=0a726722 vocab=9fbc2884
-/
lemma negDblY_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negDblY P = -(P x ^ 2) ^ 3 := by
  linear_combination (norm :=
      (rw [negDblY, dblU_of_Z_eq_zero hPz, dblX_of_Z_eq_zero hP hPz, negY_of_Z_eq_zero hPz]; ring1))
    (8 * P y ^ 2 - 4 * P x ^ 3) * (equation_of_Z_eq_zero hPz).mp hP

/--
@isnad1 id=eq.4h4v.s9.3a48877bd976 from=seed src=0 shape=c4fcf189 vocab=8f867351
-/
lemma negDblY_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : W'.negDblY P = (-W'.dblU P) ^ 3 := by
  rw [negDblY, dblX_of_Y_eq hQz hx hy hy', Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

private lemma toAffine_negAddY_of_eq {P : Fin 3 → F} (hPz : P z ≠ 0) {n d : F} (hd : d ≠ 0) :
    W.toAffine.negAddY (P x / P z ^ 2) (P x / P z ^ 2) (P y / P z ^ 3) (-n / (P z * d)) =
      (-n * (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * d ^ 2 - P x * d ^ 2)
        + P y * d ^ 3) / (P z * d) ^ 3 := by
  rw [Affine.negAddY, toAffine_addX_of_eq hPz hd]
  simp [field]

/--
@isnad1 id=eq.6h4v.s9.941ed76a833a from=seed src=0 shape=ec4b7412 vocab=332b07ef
-/
lemma negDblY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) : W.negDblY P / W.dblZ P ^ 3 =
    W.toAffine.negAddY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [negDblY, dblX, toAffine_slope_of_eq hPz hQz hx hy, dblZ, ← (X_eq_iff hPz hQz).mp hx,
    toAffine_negAddY_of_eq hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hx hy]

variable (W') in
/-- The `Y`-coordinate of a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
noncomputable def dblY (P : Fin 3 → R) : R :=
  W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

/--
@isnad1 id=eq.0h4v.s6.4438e08005b2 from=seed src=0 shape=1e54a7e6 vocab=fecb2cbc
-/
lemma dblY_smul (P : Fin 3 → R) (u : R) : W'.dblY (u • P) = (u ^ 4) ^ 3 * W'.dblY P := by
  simp only [dblY, negY_eq, negDblY_smul, dblX_smul, dblZ_smul]
  ring1

/--
@isnad1 id=eq.2h3v.s7.59f6e94cec4c from=seed src=0 shape=c2440c15 vocab=752480d2
-/
lemma dblY_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblY P = (P x ^ 2) ^ 3 := by
  rw [dblY, negY_eq, negDblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz]
  ring1

/--
@isnad1 id=eq.4h4v.s9.4616838f6d89 from=seed src=0 shape=c6b0e566 vocab=ac132692
-/
lemma dblY_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : W'.dblY P = W'.dblU P ^ 3 := by
  rw [dblY, negY_eq, negDblY_of_Y_eq hQz hx hy hy', dblZ_of_Y_eq hQz hx hy hy']
  ring1

/--
@isnad1 id=eq.6h4v.s9.fa654a282f62 from=seed src=0 shape=ec4b7412 vocab=e1557219
-/
lemma dblY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.dblY P / W.dblZ P ^ 3 = W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  erw [dblY, negY_of_Z_ne_zero <| dblZ_ne_zero_of_Y_ne' hP hQ hPz hx hy,
    dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, negDblY_of_Z_ne_zero hP hQ hPz hQz hx hy, Affine.addY]

variable (W') in
/-- The coordinates of a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
noncomputable def dblXYZ (P : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblX P, W'.dblY P, W'.dblZ P]

/--
@isnad1 id=eq.0h3v.s5.0b76310e4fd1 from=seed src=0 shape=703fff70 vocab=9ce326da
-/
lemma dblXYZ_X (P : Fin 3 → R) : W'.dblXYZ P x = W'.dblX P :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.01b22de345cb from=seed src=0 shape=703fff70 vocab=a2bb9ab4
-/
lemma dblXYZ_Y (P : Fin 3 → R) : W'.dblXYZ P y = W'.dblY P :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.613128c351e2 from=seed src=0 shape=703fff70 vocab=bad81839
-/
lemma dblXYZ_Z (P : Fin 3 → R) : W'.dblXYZ P z = W'.dblZ P :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.3dbd3879d543 from=seed src=0 shape=fc68f472 vocab=c078c66f
-/
lemma dblXYZ_smul (P : Fin 3 → R) (u : R) : W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P := by
  rw [dblXYZ, dblX_smul, dblY_smul, dblZ_smul, smul_fin3, dblXYZ_X, dblXYZ_Y, dblXYZ_Z]

/--
@isnad1 id=eq.2h3v.s7.8f5a063814a4 from=seed src=0 shape=e0c005d9 vocab=396b3c80
-/
lemma dblXYZ_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblXYZ P = P x ^ 2 • ![1, 1, 0] := by
  simp [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz,
    smul_fin3]

/--
@isnad1 id=eq.4h4v.s9.e17044b657ad from=seed src=0 shape=a9fd1e3b vocab=4e1a1bc2
-/
lemma dblXYZ_of_Y_eq' [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) :
    W'.dblXYZ P = ![W'.dblU P ^ 2, W'.dblU P ^ 3, 0] := by
  rw [dblXYZ, dblX_of_Y_eq hQz hx hy hy', dblY_of_Y_eq hQz hx hy hy', dblZ_of_Y_eq hQz hx hy hy']

/--
@isnad1 id=eq.4h4v.s9.222c71988fe2 from=seed src=0 shape=7558592c vocab=6abc19ee
-/
lemma dblXYZ_of_Y_eq {P Q : Fin 3 → F} (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 = Q y * P z ^ 3) (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) :
    W.dblXYZ P = W.dblU P • ![1, 1, 0] := by
  simp [dblXYZ_of_Y_eq' hQz hx hy hy', smul_fin3]

/--
@isnad1 id=eq.6h4v.s10.0dda2ac29ee8 from=seed src=0 shape=a455644f vocab=cf3663b0
-/
lemma dblXYZ_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.dblXYZ P = W.dblZ P •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  have hZ {n : ℕ} : IsUnit <| W.dblZ P ^ n := (isUnit_dblZ_of_Y_ne' hP hQ hPz hx hy).pow n
  erw [dblXYZ, smul_fin3, ← dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel,
    ← dblY_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel, mul_one]

/-! ## Addition formulae in Jacobian coordinates -/

/-- The unit associated to a representative of `P + Q` for two Jacobian point representatives `P`
and `Q` on a Weierstrass curve `W` that are not `2`-torsion.

More specifically, the unit `u` such that `W.add P Q = u • ![1, 1, 0]` where
`P x / P z ^ 2 = Q x / Q z ^ 2` but `P ≠ W.neg P`. -/
def addU (P Q : Fin 3 → F) : F :=
  -((P y * Q z ^ 3 - Q y * P z ^ 3) / (P z * Q z))

/--
@isnad1 id=eq.4h5v.s8.06adea6df1dd from=seed src=0 shape=40abe955 vocab=e3631475
-/
lemma addU_smul {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {u v : F} (hu : u ≠ 0)
    (hv : v ≠ 0) : addU (u • P) (v • Q) = (u * v) ^ 2 * addU P Q := by
  simp [field, addU, smul_fin3_ext]

/--
@isnad1 id=eq.1h3v.s6.a45455b75d2c from=seed src=0 shape=b62ce368 vocab=b1118d89
-/
lemma addU_of_Z_eq_zero_left {P Q : Fin 3 → F} (hPz : P z = 0) : addU P Q = 0 := by
  rw [addU, hPz, zero_mul, div_zero, neg_zero]

/--
@isnad1 id=eq.1h3v.s6.098c60b8ef1b from=seed src=0 shape=8401bad9 vocab=b1118d89
-/
lemma addU_of_Z_eq_zero_right {P Q : Fin 3 → F} (hQz : Q z = 0) : addU P Q = 0 := by
  rw [addU, hQz, mul_zero, div_zero, neg_zero]

/--
@isnad1 id=ne.3h3v.s8.1f68e4ea3446 from=seed src=0 shape=e2f400d7 vocab=e09b416a
-/
lemma addU_ne_zero_of_Y_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : addU P Q ≠ 0 :=
  neg_ne_zero.mpr <| div_ne_zero (sub_ne_zero.mpr hy) <| mul_ne_zero hPz hQz

/--
@isnad1 id=isunit.3h3v.s8.b9da0208d7c7 from=seed src=0 shape=c0f30cb2 vocab=c25b763e
-/
lemma isUnit_addU_of_Y_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : IsUnit (addU P Q) :=
  (addU_ne_zero_of_Y_ne hPz hQz hy).isUnit

/-- The `Z`-coordinate of a representative of `P + Q` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addZ (P Q : Fin 3 → R) : R :=
  P x * Q z ^ 2 - Q x * P z ^ 2

/--
@isnad1 id=eq.0h5v.s7.74a261bcd90f from=seed src=0 shape=46d48605 vocab=59e295df
-/
lemma addZ_smul (P Q : Fin 3 → R) (u v : R) : addZ (u • P) (v • Q) = (u * v) ^ 2 * addZ P Q := by
  simp only [addZ, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.0h2v.s5.402b5fa87cdc from=seed src=0 shape=3f53edd6 vocab=eb0e7695
-/
lemma addZ_self (P : Fin 3 → R) : addZ P P = 0 :=
  sub_self <| P x * P z ^ 2

/--
@isnad1 id=eq.1h3v.s7.4946df61bbf9 from=seed src=0 shape=fc2b6a44 vocab=da2dd997
-/
lemma addZ_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) : addZ P Q = P x * Q z * Q z := by
  rw [addZ, hPz]
  ring1

/--
@isnad1 id=eq.1h3v.s7.ae5993a45a77 from=seed src=0 shape=05bdb814 vocab=7afc22cc
-/
lemma addZ_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQz : Q z = 0) :
    addZ P Q = -(Q x * P z) * P z := by
  rw [addZ, hQz]
  ring1

/--
@isnad1 id=eq.1h3v.s7.2e2bfb75be89 from=seed src=0 shape=bf881813 vocab=956d5c81
-/
lemma addZ_of_X_eq {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : addZ P Q = 0 := by
  rw [addZ, hx, sub_self]

/--
@isnad1 id=ne.1h3v.s7.6d3fd1c4d312 from=seed src=0 shape=bf881813 vocab=956d5c81
-/
lemma addZ_ne_zero_of_X_ne {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : addZ P Q ≠ 0 :=
  sub_ne_zero.mpr hx

/--
@isnad1 id=isunit.1h3v.s7.89f0488bca13 from=seed src=0 shape=3ac1ffee vocab=7ab7540f
-/
lemma isUnit_addZ_of_X_ne {P Q : Fin 3 → F} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    IsUnit <| addZ P Q :=
  (addZ_ne_zero_of_X_ne hx).isUnit

private lemma toAffine_slope_of_ne [DecidableEq F] {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3) =
      (P y * Q z ^ 3 - Q y * P z ^ 3) / (P z * Q z * addZ P Q) := by
  rw [Affine.slope_of_X_ne <| by rwa [ne_eq, ← X_eq_iff hPz hQz],
    div_sub_div _ _ (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz), mul_comm <| _ ^ 2, addZ]
  simp [field]

variable (W') in
/-- The `X`-coordinate of a representative of `P + Q` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addX (P Q : Fin 3 → R) : R :=
  P x * Q x ^ 2 * P z ^ 2 - 2 * P y * Q y * P z * Q z + P x ^ 2 * Q x * Q z ^ 2
    - W'.a₁ * P x * Q y * P z ^ 2 * Q z - W'.a₁ * P y * Q x * P z * Q z ^ 2
    + 2 * W'.a₂ * P x * Q x * P z ^ 2 * Q z ^ 2 - W'.a₃ * Q y * P z ^ 4 * Q z
    - W'.a₃ * P y * P z * Q z ^ 4 + W'.a₄ * Q x * P z ^ 4 * Q z ^ 2
    + W'.a₄ * P x * P z ^ 2 * Q z ^ 4 + 2 * W'.a₆ * P z ^ 4 * Q z ^ 4

/--
@isnad1 id=eq.2h4v.s10.6185a1e1423a from=seed src=0 shape=bc97a4c6 vocab=f7f1e305
-/
lemma addX_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * (P z * Q z) ^ 2 =
      (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2
        + W'.a₁ * (P y * Q z ^ 3 - Q y * P z ^ 3) * P z * Q z * addZ P Q
        - W'.a₂ * P z ^ 2 * Q z ^ 2 * addZ P Q ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2
        - Q x * P z ^ 2 * addZ P Q ^ 2 := by
  linear_combination (norm := (rw [addX, addZ]; ring1)) -Q z ^ 6 * (equation_iff P).mp hP
    - P z ^ 6 * (equation_iff Q).mp hQ

/--
@isnad1 id=eq.4h4v.s10.ac28f5565829 from=seed src=0 shape=6d0a47ab vocab=5864c2a0
-/
lemma addX_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) : W.addX P Q =
      ((P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2
        + W.a₁ * (P y * Q z ^ 3 - Q y * P z ^ 3) * P z * Q z * addZ P Q
        - W.a₂ * P z ^ 2 * Q z ^ 2 * addZ P Q ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2
        - Q x * P z ^ 2 * addZ P Q ^ 2) / (P z * Q z) ^ 2 := by
  rw [← addX_eq' hP hQ, mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

/--
@isnad1 id=eq.0h6v.s7.b67b74354c9e from=seed src=0 shape=b709a118 vocab=1bd00bbf
-/
lemma addX_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addX (u • P) (v • Q) = ((u * v) ^ 2) ^ 2 * W'.addX P Q := by
  simp only [addX, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.1h3v.s5.a8c64b2764c5 from=seed src=0 shape=38ad19b0 vocab=82330c31
-/
lemma addX_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.addX P P = 0 := by
  linear_combination (norm := (rw [addX]; ring1)) -2 * P z ^ 2 * (equation_iff _).mp hP

/--
@isnad1 id=eq.1h4v.s7.28062a59bd10 from=seed src=0 shape=efba674f vocab=88328437
-/
lemma addX_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) :
    W'.addX P Q = (P x * Q z) ^ 2 * Q x := by
  rw [addX, hPz]
  ring1

/--
@isnad1 id=eq.1h4v.s7.17354ec4d352 from=seed src=0 shape=eccef3e2 vocab=5019846e
-/
lemma addX_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQz : Q z = 0) :
    W'.addX P Q = (-(Q x * P z)) ^ 2 * P x := by
  rw [addX, hQz]
  ring1

/--
@isnad1 id=eq.3h4v.s8.323db9c1de10 from=seed src=0 shape=8a0e67fb vocab=7b50c8b2
-/
lemma addX_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.addX P Q * (P z * Q z) ^ 2 = (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2 := by
  rw [addX_eq' hP hQ, addZ_of_X_eq hx]
  ring1

/--
@isnad1 id=eq.5h4v.s8.27a9975e8820 from=seed src=0 shape=5becab3c vocab=f3a43c72
-/
lemma addX_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : W.addX P Q = addU P Q ^ 2 := by
  rw [addU, neg_sq, div_pow, ← addX_of_X_eq' hP hQ hx,
    mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

private lemma toAffine_addX_of_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {n d : F}
    (hd : d ≠ 0) : W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2) (n / (P z * Q z * d)) =
      (n ^ 2 + W.a₁ * n * P z * Q z * d - W.a₂ * P z ^ 2 * Q z ^ 2 * d ^ 2 - P x * Q z ^ 2 * d ^ 2
        - Q x * P z ^ 2 * d ^ 2) / (P z * Q z) ^ 2 / d ^ 2 := by
  simp [field]

/--
@isnad1 id=eq.5h4v.s9.4db010548ec5 from=seed src=0 shape=d0b41477 vocab=67056327
-/
lemma addX_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : W.addX P Q / addZ P Q ^ 2 =
      W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
        (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [addX_eq hP hQ hPz hQz, toAffine_slope_of_ne hPz hQz hx,
    toAffine_addX_of_ne hPz hQz <| addZ_ne_zero_of_X_ne hx]

variable (W') in
/-- The `Y`-coordinate of a representative of `-(P + Q)` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def negAddY (P Q : Fin 3 → R) : R :=
  -P y * Q x ^ 3 * P z ^ 3 + 2 * P y * Q y ^ 2 * P z ^ 3 - 3 * P x ^ 2 * Q x * Q y * P z ^ 2 * Q z
    + 3 * P x * P y * Q x ^ 2 * P z * Q z ^ 2 + P x ^ 3 * Q y * Q z ^ 3
    - 2 * P y ^ 2 * Q y * Q z ^ 3 + W'.a₁ * P x * Q y ^ 2 * P z ^ 4
    + W'.a₁ * P y * Q x * Q y * P z ^ 3 * Q z - W'.a₁ * P x * P y * Q y * P z * Q z ^ 3
    - W'.a₁ * P y ^ 2 * Q x * Q z ^ 4 - 2 * W'.a₂ * P x * Q x * Q y * P z ^ 4 * Q z
    + 2 * W'.a₂ * P x * P y * Q x * P z * Q z ^ 4 + W'.a₃ * Q y ^ 2 * P z ^ 6
    - W'.a₃ * P y ^ 2 * Q z ^ 6 - W'.a₄ * Q x * Q y * P z ^ 6 * Q z
    - W'.a₄ * P x * Q y * P z ^ 4 * Q z ^ 3 + W'.a₄ * P y * Q x * P z ^ 3 * Q z ^ 4
    + W'.a₄ * P x * P y * P z * Q z ^ 6 - 2 * W'.a₆ * Q y * P z ^ 6 * Q z ^ 3
    + 2 * W'.a₆ * P y * P z ^ 3 * Q z ^ 6

/--
@isnad1 id=eq.0h4v.s9.d702bb5e5df2 from=seed src=0 shape=b2df85ad vocab=0000d518
-/
lemma negAddY_eq' (P Q : Fin 3 → R) : W'.negAddY P Q * (P z * Q z) ^ 3 =
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (W'.addX P Q * (P z * Q z) ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2)
      + P y * Q z ^ 3 * addZ P Q ^ 3 := by
  rw [negAddY, addX, addZ]
  ring1

/--
@isnad1 id=eq.2h4v.s9.678b50561a30 from=seed src=0 shape=56e47d14 vocab=413c7a8e
-/
lemma negAddY_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) : W.negAddY P Q =
    ((P y * Q z ^ 3 - Q y * P z ^ 3) * (W.addX P Q * (P z * Q z) ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2)
      + P y * Q z ^ 3 * addZ P Q ^ 3) / (P z * Q z) ^ 3 := by
  rw [← negAddY_eq', mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

/--
@isnad1 id=eq.0h6v.s7.94067c0a07a1 from=seed src=0 shape=b709a118 vocab=35febb08
-/
lemma negAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.negAddY (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * W'.negAddY P Q := by
  simp only [negAddY, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.0h3v.s5.1c71f562017a from=seed src=0 shape=1c306575 vocab=52045a10
-/
lemma negAddY_self (P : Fin 3 → R) : W'.negAddY P P = 0 := by
  rw [negAddY]
  ring1

/--
@isnad1 id=eq.2h4v.s7.801f00719fa3 from=seed src=0 shape=5c9efe97 vocab=097268d1
-/
lemma negAddY_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negAddY P Q = (P x * Q z) ^ 3 * W'.negY Q := by
  linear_combination (norm := (rw [negAddY, negY, hPz]; ring1))
    (W'.negY Q - Q y) * Q z ^ 3 * (equation_of_Z_eq_zero hPz).mp hP

/--
@isnad1 id=eq.2h4v.s7.a1f0945c3e8e from=seed src=0 shape=18cc477a vocab=6f1adb61
-/
lemma negAddY_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.negAddY P Q = (-(Q x * P z)) ^ 3 * W'.negY P := by
  linear_combination (norm := (rw [negAddY, negY, hQz]; ring1))
    (P y - W'.negY P) * P z ^ 3 * (equation_of_Z_eq_zero hQz).mp hQ

/--
@isnad1 id=eq.3h4v.s8.1075caff6a40 from=seed src=0 shape=8a0e67fb vocab=23999603
-/
lemma negAddY_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.negAddY P Q * (P z * Q z) ^ 3 = (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 3 := by
  rw [negAddY_eq', addX_eq' hP hQ, addZ_of_X_eq hx]
  ring1

/--
@isnad1 id=eq.5h4v.s8.ba92e3cfccfa from=seed src=0 shape=414d4366 vocab=3fc85236
-/
lemma negAddY_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : W.negAddY P Q = (-addU P Q) ^ 3 := by
  rw [addU, neg_neg, div_pow, ← negAddY_of_X_eq' hP hQ hx,
    mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

private lemma toAffine_negAddY_of_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {n d : F}
    (hd : d ≠ 0) :
    W.toAffine.negAddY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (n / (P z * Q z * d)) =
      (n * (n ^ 2 + W.a₁ * n * P z * Q z * d - W.a₂ * P z ^ 2 * Q z ^ 2 * d ^ 2
        - P x * Q z ^ 2 * d ^ 2 - Q x * P z ^ 2 * d ^ 2 - P x * Q z ^ 2 * d ^ 2)
        + P y * Q z ^ 3 * d ^ 3) / (P z * Q z) ^ 3 / d ^ 3 := by
  rw [Affine.negAddY, toAffine_addX_of_ne hPz hQz hd]
  simp [field]

/--
@isnad1 id=eq.5h4v.s9.52554ed82917 from=seed src=0 shape=2e07af8d vocab=bb06f22b
-/
lemma negAddY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.negAddY P Q / addZ P Q ^ 3 =
      W.toAffine.negAddY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
        (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [negAddY_eq hPz hQz, addX_eq' hP hQ, toAffine_slope_of_ne hPz hQz hx,
    toAffine_negAddY_of_ne hPz hQz <| addZ_ne_zero_of_X_ne hx]

variable (W') in
/-- The `Y`-coordinate of a representative of `P + Q` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addY (P Q : Fin 3 → R) : R :=
  W'.negY ![W'.addX P Q, W'.negAddY P Q, addZ P Q]

/--
@isnad1 id=eq.0h6v.s7.03198ddb0b63 from=seed src=0 shape=b709a118 vocab=889370b7
-/
lemma addY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addY (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * W'.addY P Q := by
  simp only [addY, negY_eq, negAddY_smul, addX_smul, addZ_smul]
  ring1

/--
@isnad1 id=eq.1h3v.s5.a6c41fa869c1 from=seed src=0 shape=38ad19b0 vocab=da996ca9
-/
lemma addY_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P P = 0 := by
  rw [addY, negY_eq, addX_self hP, negAddY_self, addZ_self]
  ring1

/--
@isnad1 id=eq.2h4v.s7.b7d9ead74e4a from=seed src=0 shape=13345c82 vocab=3020a72f
-/
lemma addY_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.addY P Q = (P x * Q z) ^ 3 * Q y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_left hP hPz, negY, addX_of_Z_eq_zero_left hPz,
    addZ_of_Z_eq_zero_left hPz]
  ring1

/--
@isnad1 id=eq.2h4v.s7.0356f41db145 from=seed src=0 shape=aff32c85 vocab=360452f5
-/
lemma addY_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.addY P Q = (-(Q x * P z)) ^ 3 * P y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_right hQ hQz, negY, addX_of_Z_eq_zero_right hQz,
    addZ_of_Z_eq_zero_right hQz]
  ring1

/--
@isnad1 id=eq.3h4v.s8.b797a2ffb902 from=seed src=0 shape=5722fb0a vocab=efb40dce
-/
lemma addY_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.addY P Q * (P z * Q z) ^ 3 = (-(P y * Q z ^ 3 - Q y * P z ^ 3)) ^ 3 := by
  linear_combination (norm := (rw [addY, negY_eq, addZ_of_X_eq hx]; ring1))
    -negAddY_of_X_eq' hP hQ hx

/--
@isnad1 id=eq.5h4v.s8.0312d10dc113 from=seed src=0 shape=5becab3c vocab=463d2692
-/
lemma addY_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : W.addY P Q = addU P Q ^ 3 := by
  rw [addU, ← neg_div, div_pow, ← addY_of_X_eq' hP hQ hx,
    mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

/--
@isnad1 id=eq.5h4v.s9.f86d6cb3d577 from=seed src=0 shape=2e07af8d vocab=bc512ab7
-/
lemma addY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.addY P Q / addZ P Q ^ 3 = W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  erw [addY, negY_of_Z_ne_zero <| addZ_ne_zero_of_X_ne hx, addX_of_Z_ne_zero hP hQ hPz hQz hx,
    negAddY_of_Z_ne_zero hP hQ hPz hQz hx, Affine.addY]

variable (W') in
/-- The coordinates of a representative of `P + Q` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `![0, 0, 0]`. -/
noncomputable def addXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.addX P Q, W'.addY P Q, addZ P Q]

/--
@isnad1 id=eq.0h4v.s5.c15cbba8445f from=seed src=0 shape=7edeb210 vocab=8fd162b8
-/
lemma addXYZ_X (P Q : Fin 3 → R) : W'.addXYZ P Q x = W'.addX P Q :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.537bbe759112 from=seed src=0 shape=7edeb210 vocab=522d3492
-/
lemma addXYZ_Y (P Q : Fin 3 → R) : W'.addXYZ P Q y = W'.addY P Q :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.2a6e03117b26 from=seed src=0 shape=d309bc4c vocab=2e1fc298
-/
lemma addXYZ_Z (P Q : Fin 3 → R) : W'.addXYZ P Q z = addZ P Q :=
  rfl

/--
@isnad1 id=eq.0h6v.s7.71190b10bdc9 from=seed src=0 shape=70df6811 vocab=f5e535e3
-/
lemma addXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q := by
  rw [addXYZ, addX_smul, addY_smul, addZ_smul, smul_fin3, addXYZ_X, addXYZ_Y, addXYZ_Z]

/--
@isnad1 id=eq.1h3v.s6.015b6bd98d9f from=seed src=0 shape=a62b5d5b vocab=7fb702d1
-/
lemma addXYZ_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.addXYZ P P = ![0, 0, 0] := by
  rw [addXYZ, addX_self hP, addY_self hP, addZ_self]

/--
@isnad1 id=eq.2h4v.s7.1ce955d027dc from=seed src=0 shape=f1d197c2 vocab=f701df5e
-/
lemma addXYZ_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.addXYZ P Q = (P x * Q z) • Q := by
  rw [addXYZ, addX_of_Z_eq_zero_left hPz, addY_of_Z_eq_zero_left hP hPz, addZ_of_Z_eq_zero_left hPz,
    smul_fin3]

/--
@isnad1 id=eq.2h4v.s7.b4a1ebdd4083 from=seed src=0 shape=4a575b96 vocab=a7945024
-/
lemma addXYZ_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.addXYZ P Q = -(Q x * P z) • P := by
  rw [addXYZ, addX_of_Z_eq_zero_right hQz, addY_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQz, smul_fin3]

/--
@isnad1 id=eq.5h4v.s8.8d67dee58c7e from=seed src=0 shape=cc03314f vocab=a1f0d9d1
-/
lemma addXYZ_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W.addXYZ P Q = addU P Q • ![1, 1, 0] := by
  simp [addXYZ, addX_of_X_eq hP hQ hPz hQz hx, addY_of_X_eq hP hQ hPz hQz hx, addZ_of_X_eq hx,
    smul_fin3]

/--
@isnad1 id=eq.5h4v.s10.d322a7be7a7d from=seed src=0 shape=57d8c3d8 vocab=31824dca
-/
lemma addXYZ_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : W.addXYZ P Q = addZ P Q •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  have hZ {n : ℕ} : IsUnit <| addZ P Q ^ n := (isUnit_addZ_of_X_ne hx).pow n
  erw [addXYZ, smul_fin3, ← addX_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel,
    ← addY_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel, mul_one]

/-! ## Maps and base changes -/

variable (f : R →+* S) (P Q : Fin 3 → R)

/--
@isnad1 id=eq.0h5v.s7.bf5d3ff33b66 from=seed src=0 shape=92bdc66f vocab=3ceaf3e3
-/
@[simp]
lemma map_negY : (W'.map f).negY (f ∘ P) = f (W'.negY P) := by
  simp only [negY]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.cd0a29cbaa17 from=seed src=0 shape=92bdc66f vocab=07c0dafc
-/
@[simp]
lemma map_dblU : (W'.map f).dblU (f ∘ P) = f (W'.dblU P) := by
  simp only [dblU_eq]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.7653598ac13d from=seed src=0 shape=92bdc66f vocab=f90686ef
-/
@[simp]
lemma map_dblZ : (W'.map f).dblZ (f ∘ P) = f (W'.dblZ P) := by
  simp only [dblZ, negY]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.d11a3211b553 from=seed src=0 shape=92bdc66f vocab=2f2a38a3
-/
@[simp]
lemma map_dblX : (W'.map f).dblX (f ∘ P) = f (W'.dblX P) := by
  simp only [dblX, map_dblU, map_negY]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.215abe8f35b3 from=seed src=0 shape=92bdc66f vocab=cdb23ce3
-/
@[simp]
lemma map_negDblY : (W'.map f).negDblY (f ∘ P) = f (W'.negDblY P) := by
  simp only [negDblY, map_dblU, map_dblX, map_negY]
  simp

/--
@isnad1 id=eq.0h5v.s7.ba6aa922a3e8 from=seed src=0 shape=92bdc66f vocab=e230d1fb
-/
@[simp]
lemma map_dblY : (W'.map f).dblY (f ∘ P) = f (W'.dblY P) := by
  simp only [dblY, negY_eq, map_negDblY, map_dblX, map_dblZ]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.2d133ee978ec from=seed src=0 shape=63cb483b vocab=f99ef2dc
-/
@[simp]
lemma map_dblXYZ : (W'.map f).dblXYZ (f ∘ P) = f ∘ dblXYZ W' P := by
  simp only [dblXYZ, map_dblX, map_dblY, map_dblZ, comp_fin3]

/--
@isnad1 id=eq.0h5v.s7.20ecf81e7367 from=seed src=0 shape=deeb099f vocab=a0957e15
-/
@[simp]
lemma map_addU (f : F →+* K) (P Q : Fin 3 → F) : addU (f ∘ P) (f ∘ Q) = f (addU P Q) := by
  simp only [addU]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.f0bf7610712f from=seed src=0 shape=deeb099f vocab=bf909899
-/
@[simp]
lemma map_addZ : addZ (f ∘ P) (f ∘ Q) = f (addZ P Q) := by
  simp only [addZ]
  map_simp

/--
@isnad1 id=eq.0h6v.s7.9ffdefded5c8 from=seed src=0 shape=a2e09276 vocab=fc02546c
-/
@[simp]
lemma map_addX : (W'.map f).addX (f ∘ P) (f ∘ Q) = f (W'.addX P Q) := by
  simp only [addX]
  map_simp

/--
@isnad1 id=eq.0h6v.s7.52c9f96d8ed0 from=seed src=0 shape=a2e09276 vocab=538702ec
-/
@[simp]
lemma map_negAddY : (W'.map f).negAddY (f ∘ P) (f ∘ Q) = f (W'.negAddY P Q) := by
  simp only [negAddY]
  map_simp

/--
@isnad1 id=eq.0h6v.s7.e0597a72602c from=seed src=0 shape=a2e09276 vocab=2133974c
-/
@[simp]
lemma map_addY : (W'.map f).addY (f ∘ P) (f ∘ Q) = f (W'.addY P Q) := by
  simp only [addY, negY_eq, map_negAddY, map_addX, map_addZ]
  map_simp

/--
@isnad1 id=eq.0h6v.s7.60f98dc7fd78 from=seed src=0 shape=4f98816f vocab=d01ad81c
-/
@[simp]
lemma map_addXYZ : (W'.map f).addXYZ (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q := by
  simp only [addXYZ, map_addX, map_addY, map_addZ, comp_fin3]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B) (P Q : Fin 3 → A)

/--
@isnad1 id=eq.0h7v.s8.a2cdf310697d from=seed src=0 shape=5bc7e8cb vocab=15d95df8
-/
lemma baseChange_negY : (W'⁄B).negY (f ∘ P) = f ((W'⁄A).negY P) := by
  rw [← RingHom.coe_coe, ← map_negY, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.5aafb7fb9825 from=seed src=0 shape=5bc7e8cb vocab=b7a88c7a
-/
lemma baseChange_dblU : (W'⁄B).dblU (f ∘ P) = f ((W'⁄A).dblU P) := by
  rw [← RingHom.coe_coe, ← map_dblU, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.ba0b09e51cc0 from=seed src=0 shape=5bc7e8cb vocab=08391b3f
-/
lemma baseChange_dblZ : (W'⁄B).dblZ (f ∘ P) = f ((W'⁄A).dblZ P) := by
  rw [← RingHom.coe_coe, ← map_dblZ, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.9eb6ecb68387 from=seed src=0 shape=5bc7e8cb vocab=ab1f93e5
-/
lemma baseChange_dblX : (W'⁄B).dblX (f ∘ P) = f ((W'⁄A).dblX P) := by
  rw [← RingHom.coe_coe, ← map_dblX, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.daef9af8d5ae from=seed src=0 shape=5bc7e8cb vocab=4d7dcd4e
-/
lemma baseChange_negDblY : (W'⁄B).negDblY (f ∘ P) = f ((W'⁄A).negDblY P) := by
  rw [← RingHom.coe_coe, ← map_negDblY, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.36b3c10bf7ad from=seed src=0 shape=5bc7e8cb vocab=110cd4fa
-/
lemma baseChange_dblY : (W'⁄B).dblY (f ∘ P) = f ((W'⁄A).dblY P) := by
  rw [← RingHom.coe_coe, ← map_dblY, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.33cc505a41b9 from=seed src=0 shape=a29f2889 vocab=056fb2f8
-/
lemma baseChange_dblXYZ : (W'⁄B).dblXYZ (f ∘ P) = f ∘ (W'⁄A).dblXYZ P := by
  rw [← RingHom.coe_coe, ← map_dblXYZ, map_baseChange]

/--
@isnad1 id=eq.0h8v.s8.8350adb4937c from=seed src=0 shape=ea2a2746 vocab=270a74a7
-/
lemma baseChange_addX : (W'⁄B).addX (f ∘ P) (f ∘ Q) = f ((W'⁄A).addX P Q) := by
  rw [← RingHom.coe_coe, ← map_addX, map_baseChange]

/--
@isnad1 id=eq.0h8v.s8.916f43155704 from=seed src=0 shape=ea2a2746 vocab=d121d7d8
-/
lemma baseChange_negAddY : (W'⁄B).negAddY (f ∘ P) (f ∘ Q) = f ((W'⁄A).negAddY P Q) := by
  rw [← RingHom.coe_coe, ← map_negAddY, map_baseChange]

/--
@isnad1 id=eq.0h8v.s8.ebd101cf7cff from=seed src=0 shape=ea2a2746 vocab=9a70bf64
-/
lemma baseChange_addY : (W'⁄B).addY (f ∘ P) (f ∘ Q) = f ((W'⁄A).addY P Q) := by
  rw [← RingHom.coe_coe, ← map_addY, map_baseChange]

/--
@isnad1 id=eq.0h8v.s8.4fe0f82c6189 from=seed src=0 shape=25e54fc1 vocab=b95a2441
-/
lemma baseChange_addXYZ : (W'⁄B).addXYZ (f ∘ P) (f ∘ Q) = f ∘ (W'⁄A).addXYZ P Q := by
  rw [← RingHom.coe_coe, ← map_addXYZ, map_baseChange]

end Jacobian

end WeierstrassCurve
