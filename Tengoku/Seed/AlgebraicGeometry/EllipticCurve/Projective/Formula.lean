/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Projective.Basic

/-!
# Negation and addition formulae for nonsingular points in projective coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular projective points on `W` can be
given negation and addition operations defined by an analogue of the secant-and-tangent process in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`, but the polynomials involved are
homogeneous, so any instances of division become multiplication in the `Z`-coordinate. Most
computational proofs are immediate from their analogous proofs for affine coordinates.

This file defines polynomials associated to negation, doubling, and addition of projective point
representatives. The group operations and the group law on actual nonsingular projective points will
be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`.

## Main definitions

* `WeierstrassCurve.Projective.negY`: the `Y`-coordinate of `-P`.
* `WeierstrassCurve.Projective.dblZ`: the `Z`-coordinate of `2 • P`.
* `WeierstrassCurve.Projective.dblX`: the `X`-coordinate of `2 • P`.
* `WeierstrassCurve.Projective.negDblY`: the `Y`-coordinate of `-(2 • P)`.
* `WeierstrassCurve.Projective.dblY`: the `Y`-coordinate of `2 • P`.
* `WeierstrassCurve.Projective.addZ`: the `Z`-coordinate of `P + Q`.
* `WeierstrassCurve.Projective.addX`: the `X`-coordinate of `P + Q`.
* `WeierstrassCurve.Projective.negAddY`: the `Y`-coordinate of `-(P + Q)`.
* `WeierstrassCurve.Projective.addY`: the `Y`-coordinate of `P + Q`.

## Implementation notes

The definitions of `WeierstrassCurve.Projective.dblX`, `WeierstrassCurve.Projective.negDblY`,
`WeierstrassCurve.Projective.addZ`, `WeierstrassCurve.Projective.addX`, and
`WeierstrassCurve.Projective.negAddY` are given explicitly by large polynomials that are homogeneous
of degree `4`. Clearing the denominators of their corresponding affine rational functions in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` would give polynomials that are
homogeneous of degrees `5`, `6`, `6`, `8`, and `8` respectively, so their actual definitions are off
by powers of certain polynomial factors that are homogeneous of degree `1` or `2`. These factors
divide their corresponding affine polynomials only modulo the homogeneous Weierstrass equation, so
their large quotient polynomials are calculated explicitly in a computer algebra system. All of this
is done to ensure that the definitions of both `WeierstrassCurve.Projective.dblXYZ` and
`WeierstrassCurve.Projective.addXYZ` are homogeneous of degree `4`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, projective, negation, doubling, addition, group law
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
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Projective R} {W : Projective F}

namespace Projective

/-! ## Negation formulae in projective coordinates -/

variable (W') in
/-- The `Y`-coordinate of a representative of `-P` for a projective point representative `P` on a
Weierstrass curve. -/
def negY (P : Fin 3 → R) : R :=
  -P y - W'.a₁ * P x - W'.a₃ * P z

/--
@isnad1 id=eq.0h5v.s7.8f6fa8578377 from=seed src=0 shape=65b826a5 vocab=1a7858f6
-/
lemma negY_eq (X Y Z : R) : W'.negY ![X, Y, Z] = -Y - W'.a₁ * X - W'.a₃ * Z :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.5ff029892d27 from=seed src=0 shape=3301346f vocab=1b8995d8
-/
lemma negY_smul (P : Fin 3 → R) (u : R) : W'.negY (u • P) = u * W'.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.2h3v.s6.331723d78869 from=seed src=0 shape=529c2bef vocab=2a239a7e
-/
lemma negY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negY P = -P y := by
  rw [negY, hPz, X_eq_zero_of_Z_eq_zero hP hPz, mul_zero, sub_zero, mul_zero, sub_zero]

/--
@isnad1 id=eq.1h3v.s7.95532e1c1507 from=seed src=0 shape=faee54c9 vocab=c1016625
-/
lemma negY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negY P / P z = W.toAffine.negY (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [negY, Affine.negY]; ring1)) -W.a₃ * div_self hPz

/--
@isnad1 id=eq.3h4v.s8.bd5179d3bf39 from=seed src=0 shape=bf45286d vocab=74413435
-/
lemma Y_sub_Y_mul_Y_sub_negY {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z = Q x * P z) :
    P z * Q z * (P y * Q z - Q y * P z) * (P y * Q z - W'.negY Q * P z) = 0 := by
  linear_combination (norm := (rw [negY]; ring1)) Q z ^ 3 * (equation_iff P).mp hP
    - P z ^ 3 * (equation_iff Q).mp hQ + (P x ^ 2 * Q z ^ 2 + P x * Q x * P z * Q z
      + Q x ^ 2 * P z ^ 2 - W'.a₁ * P y * P z * Q z ^ 2 + W'.a₂ * P x * Q z ^ 2 * P z
      + W'.a₂ * Q x * P z ^ 2 * Q z + W'.a₄ * P z ^ 2 * Q z ^ 2) * hx

/--
@isnad1 id=eq.6h4v.s8.3cd80fda080e from=seed src=0 shape=661de158 vocab=19556a5c
-/
lemma Y_eq_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ Q y * P z) :
    P y * Q z = W'.negY Q * P z :=
  sub_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <|
    mul_ne_zero (mul_ne_zero hPz hQz) <| sub_ne_zero.mpr hy

/--
@isnad1 id=eq.6h4v.s8.b520099003fc from=seed src=0 shape=d7cca17a vocab=19556a5c
-/
lemma Y_eq_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ W'.negY Q * P z) : P y * Q z = Q y * P z :=
  sub_eq_zero.mp <| (mul_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx
    ).resolve_right <| sub_ne_zero.mpr hy).resolve_left <| mul_ne_zero hPz hQz

/--
@isnad1 id=iff.2h4v.s8.52c1e5409724 from=seed src=0 shape=a224ce22 vocab=d8572e2a
-/
lemma Y_eq_iff' {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z = W.negY Q * P z ↔ P y / P z = W.toAffine.negY (Q x / Q z) (Q y / Q z) :=
  negY_of_Z_ne_zero hQz ▸ (div_eq_div_iff hPz hQz).symm

/--
@isnad1 id=eq.1h4v.s8.4c3b863d1f99 from=seed src=0 shape=a0bf634d vocab=c3e9cf16
-/
lemma Y_sub_Y_add_Y_sub_negY {P Q : Fin 3 → R} (hx : P x * Q z = Q x * P z) :
    (P y * Q z - Q y * P z) + (P y * Q z - W'.negY Q * P z) = (P y - W'.negY P) * Q z := by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * hx

/--
@isnad1 id=ne.6h4v.s8.991e293f08b5 from=seed src=0 shape=d542c5fa vocab=19556a5c
-/
lemma Y_ne_negY_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ Q y * P z) : P y ≠ W'.negY P := by
  have hy' : P y * Q z - W'.negY Q * P z = 0 := sub_eq_zero.mpr <| Y_eq_of_Y_ne hP hQ hPz hQz hx hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

/--
@isnad1 id=ne.6h4v.s8.6212770f9f4a from=seed src=0 shape=50258e93 vocab=19556a5c
-/
lemma Y_ne_negY_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ W'.negY Q * P z) : P y ≠ W'.negY P := by
  have hy' : P y * Q z - Q y * P z = 0 := sub_eq_zero.mpr <| Y_eq_of_Y_ne' hP hQ hPz hQz hx hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

/--
@isnad1 id=eq.4h4v.s8.de3cd44fd663 from=seed src=0 shape=56ee9a8e vocab=0f09c63a
-/
lemma Y_eq_negY_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W'.negY Q * P z) :
    P y = W'.negY P :=
  mul_left_injective₀ hQz <| by
    linear_combination (norm := ring1) -Y_sub_Y_add_Y_sub_negY hx + hy + hy'

/--
@isnad1 id=iff.2h3v.s8.913d66a3c24c from=seed src=0 shape=074e78d0 vocab=cbe93450
-/
lemma nonsingular_iff_of_Y_eq_negY {P : Fin 3 → F} (hPz : P z ≠ 0) (hy : P y = W.negY P) :
    W.Nonsingular P ↔ W.Equation P ∧ eval P W.polynomialX ≠ 0 := by
  have hy' : eval P W.polynomialY = (P y - W.negY P) * P z := by rw [negY, eval_polynomialY]; ring1
  rw [nonsingular_iff_of_Z_ne_zero hPz, hy', hy, sub_self, zero_mul, ne_self_iff_false, or_false]

/-! ## Doubling formulae in projective coordinates -/

variable (W) in
/-- The unit associated to a representative of `2 • P` for a projective point representative `P` on
a Weierstrass curve `W` that is `2`-torsion.

More specifically, the unit `u` such that `W.add P P = u • ![0, 1, 0]` where `P = W.neg P`. -/
noncomputable def dblU (P : Fin 3 → F) : F :=
  eval P W.polynomialX ^ 3 / P z ^ 2

/--
@isnad1 id=eq.0h3v.s8.2301158a950f from=seed src=0 shape=aea2e7fc vocab=7681efca
-/
lemma dblU_eq (P : Fin 3 → F) : W.dblU P =
    (W.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2)) ^ 3 / P z ^ 2 := by
  rw [dblU, eval_polynomialX]

/--
@isnad1 id=eq.0h4v.s6.576696c931ce from=seed src=0 shape=94adfe35 vocab=7a892998
-/
lemma dblU_smul (P : Fin 3 → F) (u : F) :
    W.dblU (u • P) = u ^ 4 * W.dblU P := by
  simp [field, dblU_eq]

/--
@isnad1 id=eq.1h3v.s6.fcd393dcfc09 from=seed src=0 shape=55d59f0b vocab=9b7decd3
-/
lemma dblU_of_Z_eq_zero {P : Fin 3 → F} (hPz : P z = 0) : W.dblU P = 0 := by
  rw [dblU_eq, hPz, zero_pow two_ne_zero, div_zero]

/--
@isnad1 id=ne.6h4v.s8.f351d6b7deb7 from=seed src=0 shape=898d8f0e vocab=5b96f754
-/
lemma dblU_ne_zero_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.dblU P ≠ 0 :=
  div_ne_zero (pow_ne_zero 3
    ((nonsingular_iff_of_Y_eq_negY hPz <| Y_eq_negY_of_Y_eq hQz hx hy hy').mp hP).right) <|
    pow_ne_zero 2 hPz

/--
@isnad1 id=isunit.6h4v.s8.9b74436f994f from=seed src=0 shape=87f3dc8a vocab=1b4141ee
-/
lemma isUnit_dblU_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    IsUnit (W.dblU P) :=
  (dblU_ne_zero_of_Y_eq hP hPz hQz hx hy hy').isUnit

variable (W') in
/-- The `Z`-coordinate of a representative of `2 • P` for a projective point representative `P` on a
Weierstrass curve. -/
def dblZ (P : Fin 3 → R) : R :=
  P z * (P y - W'.negY P) ^ 3

/--
@isnad1 id=eq.0h4v.s6.5af05cf76897 from=seed src=0 shape=94adfe35 vocab=42d40fda
-/
lemma dblZ_smul (P : Fin 3 → R) (u : R) : W'.dblZ (u • P) = u ^ 4 * W'.dblZ P := by
  simp only [dblZ, negY_smul, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.1h3v.s6.c884f48913c0 from=seed src=0 shape=55d59f0b vocab=ac4d3ee8
-/
lemma dblZ_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.dblZ P = 0 := by
  rw [dblZ, hPz, zero_mul]

/--
@isnad1 id=eq.4h4v.s8.66e6840f1282 from=seed src=0 shape=a0d76399 vocab=ce21dbd3
-/
lemma dblZ_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W'.negY Q * P z) : W'.dblZ P = 0 := by
  rw [dblZ, Y_eq_negY_of_Y_eq hQz hx hy hy', sub_self, zero_pow three_ne_zero, mul_zero]

/--
@isnad1 id=ne.6h4v.s8.6a7310c230e8 from=seed src=0 shape=d7fae6a2 vocab=c95090b2
-/
lemma dblZ_ne_zero_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ Q y * P z) : W'.dblZ P ≠ 0 :=
  mul_ne_zero hPz <| pow_ne_zero 3 <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne hP hQ hPz hQz hx hy

/--
@isnad1 id=isunit.6h4v.s8.5d2a6420821e from=seed src=0 shape=8d501224 vocab=0d4c58e9
-/
lemma isUnit_dblZ_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ Q y * P z) : IsUnit (W.dblZ P) :=
  (dblZ_ne_zero_of_Y_ne hP hQ hPz hQz hx hy).isUnit

/--
@isnad1 id=ne.6h4v.s8.59310118a003 from=seed src=0 shape=dccaf191 vocab=39e0153d
-/
lemma dblZ_ne_zero_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ W'.negY Q * P z) : W'.dblZ P ≠ 0 :=
  mul_ne_zero hPz <| pow_ne_zero 3 <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy

/--
@isnad1 id=isunit.6h4v.s8.e382c76ba787 from=seed src=0 shape=49bbf94f vocab=704a85cc
-/
lemma isUnit_dblZ_of_Y_ne' {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    IsUnit (W.dblZ P) :=
  (dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy).isUnit

private lemma toAffine_slope_of_eq [DecidableEq F] {P Q : Fin 3 → F}
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z) =
      -eval P W.polynomialX / P z / (P y - W.negY P) := by
  simp only [X_eq_iff hPz hQz, ne_eq, Y_eq_iff' hPz hQz] at hx hy
  rw [Affine.slope_of_Y_ne hx <| negY_of_Z_ne_zero hQz ▸ hy, ← negY_of_Z_ne_zero hPz]
  simp [field, eval_polynomialX]

variable (W') in
/-- The `X`-coordinate of a representative of `2 • P` for a projective point representative `P` on a
Weierstrass curve. -/
noncomputable def dblX (P : Fin 3 → R) : R :=
  2 * P x * P y ^ 3 + 3 * W'.a₁ * P x ^ 2 * P y ^ 2 + 6 * W'.a₂ * P x ^ 3 * P y
    - 8 * W'.a₂ * P y ^ 3 * P z + 9 * W'.a₃ * P x ^ 4 - 6 * W'.a₃ * P x * P y ^ 2 * P z
    - 6 * W'.a₄ * P x ^ 2 * P y * P z - 18 * W'.a₆ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * P x ^ 3 * P y - 2 * W'.a₁ ^ 2 * P y ^ 3 * P z + 3 * W'.a₁ * W'.a₂ * P x ^ 4
    - 12 * W'.a₁ * W'.a₂ * P x * P y ^ 2 * P z - 9 * W'.a₁ * W'.a₃ * P x ^ 2 * P y * P z
    - 3 * W'.a₁ * W'.a₄ * P x ^ 3 * P z - 9 * W'.a₁ * W'.a₆ * P x ^ 2 * P z ^ 2
    + 8 * W'.a₂ ^ 2 * P x ^ 2 * P y * P z + 12 * W'.a₂ * W'.a₃ * P x ^ 3 * P z
    - 12 * W'.a₂ * W'.a₃ * P y ^ 2 * P z ^ 2 + 8 * W'.a₂ * W'.a₄ * P x * P y * P z ^ 2
    - 12 * W'.a₃ ^ 2 * P x * P y * P z ^ 2 + 6 * W'.a₃ * W'.a₄ * P x ^ 2 * P z ^ 2
    + 2 * W'.a₄ ^ 2 * P y * P z ^ 3 + W'.a₁ ^ 3 * P x ^ 4 - 3 * W'.a₁ ^ 3 * P x * P y ^ 2 * P z
    - 2 * W'.a₁ ^ 2 * W'.a₂ * P x ^ 2 * P y * P z - 3 * W'.a₁ ^ 2 * W'.a₃ * P y ^ 2 * P z ^ 2
    + 2 * W'.a₁ ^ 2 * W'.a₄ * P x * P y * P z ^ 2 + 4 * W'.a₁ * W'.a₂ ^ 2 * P x ^ 3 * P z
    - 8 * W'.a₁ * W'.a₂ * W'.a₃ * P x * P y * P z ^ 2
    + 4 * W'.a₁ * W'.a₂ * W'.a₄ * P x ^ 2 * P z ^ 2 - 3 * W'.a₁ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2
    + 2 * W'.a₁ * W'.a₃ * W'.a₄ * P y * P z ^ 3 + W'.a₁ * W'.a₄ ^ 2 * P x * P z ^ 3
    + 4 * W'.a₂ ^ 2 * W'.a₃ * P x ^ 2 * P z ^ 2 - 6 * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3
    + 4 * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3 - 2 * W'.a₃ ^ 3 * P x * P z ^ 3
    + W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 - W'.a₁ ^ 4 * P x ^ 2 * P y * P z
    + W'.a₁ ^ 3 * W'.a₂ * P x ^ 3 * P z - 2 * W'.a₁ ^ 3 * W'.a₃ * P x * P y * P z ^ 2
    + W'.a₁ ^ 3 * W'.a₄ * P x ^ 2 * P z ^ 2 + W'.a₁ ^ 2 * W'.a₂ * W'.a₃ * P x ^ 2 * P z ^ 2
    - W'.a₁ ^ 2 * W'.a₃ ^ 2 * P y * P z ^ 3 + 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P x * P z ^ 3
    - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P x * P z ^ 3 - W'.a₂ * W'.a₃ ^ 3 * P z ^ 4
    + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4

/--
@isnad1 id=eq.1h3v.s9.81f998b5575c from=seed src=0 shape=e42ed040 vocab=b2cae792
-/
lemma dblX_eq' {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblX P * P z =
    (eval P W'.polynomialX ^ 2 - W'.a₁ * eval P W'.polynomialX * P z * (P y - W'.negY P)
      - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * P z * (P y - W'.negY P) ^ 2)
      * (P y - W'.negY P) := by
  linear_combination (norm := (rw [dblX, eval_polynomialX, negY]; ring1))
    9 * (W'.a₁ * P x ^ 2 + 2 * P x * P y) * (equation_iff _).mp hP

/--
@isnad1 id=eq.2h3v.s9.8b1978ad5d8d from=seed src=0 shape=a20a9fba vocab=3613fdab
-/
lemma dblX_eq {P : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) : W.dblX P =
    ((eval P W.polynomialX ^ 2 - W.a₁ * eval P W.polynomialX * P z * (P y - W.negY P)
      - W.a₂ * P z ^ 2 * (P y - W.negY P) ^ 2 - 2 * P x * P z * (P y - W.negY P) ^ 2)
      * (P y - W.negY P)) / P z := by
  rw [← dblX_eq' hP, mul_div_cancel_right₀ _ hPz]

/--
@isnad1 id=eq.0h4v.s6.8f82886b9fb3 from=seed src=0 shape=94adfe35 vocab=8e93aa60
-/
lemma dblX_smul (P : Fin 3 → R) (u : R) : W'.dblX (u • P) = u ^ 4 * W'.dblX P := by
  simp only [dblX, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.2h3v.s6.044ada923289 from=seed src=0 shape=1d4ad593 vocab=6abb9117
-/
lemma dblX_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblX P = 0 := by
  rw [dblX, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

/--
@isnad1 id=eq.6h4v.s8.517c3c5c2317 from=seed src=0 shape=1a1686fc vocab=14d16be8
-/
lemma dblX_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z)
    (hy' : P y * Q z = W'.negY Q * P z) : W'.dblX P = 0 := by
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero hPz
  rw [dblX_eq' hP, Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

private lemma toAffine_addX_of_eq {P : Fin 3 → F} (hPz : P z ≠ 0) {n d : F} (hd : d ≠ 0) :
    W.toAffine.addX (P x / P z) (P x / P z) (-n / P z / d) =
      (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * P z * d ^ 2) * d / P z
        / (P z * d ^ 3) := by
  simp [field]
  ring1

/--
@isnad1 id=eq.6h4v.s9.66e746bc12fd from=seed src=0 shape=29db2cb2 vocab=b71fc49b
-/
lemma dblX_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.dblX P / W.dblZ P = W.toAffine.addX (P x / P z) (Q x / Q z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [dblX_eq hP hPz, dblZ, toAffine_slope_of_eq hPz hQz hx hy, ← (X_eq_iff hPz hQz).mp hx,
    toAffine_addX_of_eq hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

variable (W') in
/-- The `Y`-coordinate of a representative of `-(2 • P)` for a projective point representative `P`
on a Weierstrass curve. -/
noncomputable def negDblY (P : Fin 3 → R) : R :=
  -P y ^ 4 - 3 * W'.a₁ * P x * P y ^ 3 - 9 * W'.a₃ * P x ^ 3 * P y + 3 * W'.a₃ * P y ^ 3 * P z
    - 3 * W'.a₄ * P x * P y ^ 2 * P z - 27 * W'.a₆ * P x ^ 3 * P z + 9 * W'.a₆ * P y ^ 2 * P z ^ 2
    - 3 * W'.a₁ ^ 2 * P x ^ 2 * P y ^ 2 + 4 * W'.a₁ * W'.a₂ * P y ^ 3 * P z
    - 3 * W'.a₁ * W'.a₂ * P x ^ 3 * P y - 9 * W'.a₁ * W'.a₃ * P x ^ 4
    + 6 * W'.a₁ * W'.a₃ * P x * P y ^ 2 * P z + 18 * W'.a₁ * W'.a₆ * P x * P y * P z ^ 2
    + 9 * W'.a₂ ^ 2 * P x ^ 4 - 8 * W'.a₂ ^ 2 * P x * P y ^ 2 * P z
    - 9 * W'.a₂ * W'.a₃ * P x ^ 2 * P y * P z + 9 * W'.a₂ * W'.a₄ * P x ^ 3 * P z
    - 4 * W'.a₂ * W'.a₄ * P y ^ 2 * P z ^ 2 - 27 * W'.a₂ * W'.a₆ * P x ^ 2 * P z ^ 2
    - 9 * W'.a₃ ^ 2 * P x ^ 3 * P z + 6 * W'.a₃ ^ 2 * P y ^ 2 * P z ^ 2
    - 12 * W'.a₃ * W'.a₄ * P x * P y * P z ^ 2 + 9 * W'.a₄ ^ 2 * P x ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 3 * P x ^ 3 * P y + W'.a₁ ^ 3 * P y ^ 3 * P z + 3 * W'.a₁ ^ 2 * W'.a₂ * P x ^ 4
    + 2 * W'.a₁ ^ 2 * W'.a₂ * P x * P y ^ 2 * P z + 3 * W'.a₁ ^ 2 * W'.a₃ * P x ^ 2 * P y * P z
    + 3 * W'.a₁ ^ 2 * W'.a₄ * P x ^ 3 * P z - W'.a₁ ^ 2 * W'.a₄ * P y ^ 2 * P z ^ 2
    - 12 * W'.a₁ * W'.a₂ ^ 2 * P x ^ 2 * P y * P z - 6 * W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 3 * P z
    + 4 * W'.a₁ * W'.a₂ * W'.a₃ * P y ^ 2 * P z ^ 2
    - 8 * W'.a₁ * W'.a₂ * W'.a₄ * P x * P y * P z ^ 2 + 6 * W'.a₁ * W'.a₃ ^ 2 * P x * P y * P z ^ 2
    - W'.a₁ * W'.a₄ ^ 2 * P y * P z ^ 3 + 8 * W'.a₂ ^ 3 * P x ^ 3 * P z
    - 8 * W'.a₂ ^ 2 * W'.a₃ * P x * P y * P z ^ 2 + 12 * W'.a₂ ^ 2 * W'.a₄ * P x ^ 2 * P z ^ 2
    - 9 * W'.a₂ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 - 4 * W'.a₂ * W'.a₃ * W'.a₄ * P y * P z ^ 3
    + 6 * W'.a₂ * W'.a₄ ^ 2 * P x * P z ^ 3 + W'.a₃ ^ 3 * P y * P z ^ 3
    - 3 * W'.a₃ ^ 2 * W'.a₄ * P x * P z ^ 3 + W'.a₄ ^ 3 * P z ^ 4 + W'.a₁ ^ 4 * P x * P y ^ 2 * P z
    - 3 * W'.a₁ ^ 3 * W'.a₂ * P x ^ 2 * P y * P z + W'.a₁ ^ 3 * W'.a₃ * P y ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 3 * W'.a₄ * P x * P y * P z ^ 2 + 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * P x ^ 3 * P z
    - 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ * P x ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * P z ^ 3 + W'.a₁ ^ 2 * W'.a₄ ^ 2 * P x * P z ^ 3
    + W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3 + 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3
    + W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 - 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * P z ^ 3
    - W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4

/--
@isnad1 id=eq.1h3v.s10.55538f58cd78 from=seed src=0 shape=a40c3a10 vocab=ef090c71
-/
lemma negDblY_eq' {P : Fin 3 → R} (hP : W'.Equation P) : W'.negDblY P * P z ^ 2 =
    -eval P W'.polynomialX * (eval P W'.polynomialX ^ 2
      - W'.a₁ * eval P W'.polynomialX * P z * (P y - W'.negY P)
      - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * P z * (P y - W'.negY P) ^ 2
      - P x * P z * (P y - W'.negY P) ^ 2) + P y * P z ^ 2 * (P y - W'.negY P) ^ 3 := by
  linear_combination (norm := (rw [negDblY, eval_polynomialX, negY]; ring1))
    -9 * (P y ^ 2 * P z + 2 * W'.a₁ * P x * P y * P z - 3 * P x ^ 3 - 3 * W'.a₂ * P x ^ 2 * P z)
      * (equation_iff _).mp hP

/--
@isnad1 id=eq.2h3v.s10.318f80f0fc5c from=seed src=0 shape=33d02ccc vocab=cda4b82f
-/
lemma negDblY_eq {P : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) : W.negDblY P =
    (-eval P W.polynomialX * (eval P W.polynomialX ^ 2
      - W.a₁ * eval P W.polynomialX * P z * (P y - W.negY P)
      - W.a₂ * P z ^ 2 * (P y - W.negY P) ^ 2 - 2 * P x * P z * (P y - W.negY P) ^ 2
      - P x * P z * (P y - W.negY P) ^ 2) + P y * P z ^ 2 * (P y - W.negY P) ^ 3) / P z ^ 2 := by
  rw [← negDblY_eq' hP, mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

/--
@isnad1 id=eq.0h4v.s6.b3ffa6163d59 from=seed src=0 shape=94adfe35 vocab=4a847384
-/
lemma negDblY_smul (P : Fin 3 → R) (u : R) : W'.negDblY (u • P) = u ^ 4 * W'.negDblY P := by
  simp only [negDblY, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.2h3v.s7.f640e609ce20 from=seed src=0 shape=b8f998a8 vocab=18afcd9c
-/
lemma negDblY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negDblY P = -P y ^ 4 := by
  rw [negDblY, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

/--
@isnad1 id=eq.5h4v.s9.629ca3c49bcf from=seed src=0 shape=222a2c6c vocab=f4d2135b
-/
lemma negDblY_of_Y_eq' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W'.negY Q * P z) :
    W'.negDblY P * P z ^ 2 = -eval P W'.polynomialX ^ 3 := by
  rw [negDblY_eq' hP, Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

/--
@isnad1 id=eq.6h4v.s8.f5d7bd3c8c6f from=seed src=0 shape=08ac128b vocab=99de7b63
-/
lemma negDblY_of_Y_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.negDblY P = -W.dblU P := by
  rw [dblU, ← neg_div, ← negDblY_of_Y_eq' hP hQz hx hy hy',
    mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

private lemma toAffine_negAddY_of_eq {P : Fin 3 → F} (hPz : P z ≠ 0) {n d : F} (hd : d ≠ 0) :
    W.toAffine.negAddY (P x / P z) (P x / P z) (P y / P z) (-n / P z / d) =
      (-n * (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * P z * d ^ 2
          - P x * P z * d ^ 2) + P y * P z ^ 2 * d ^ 3) / P z ^ 2 / (P z * d ^ 3) := by
  rw [Affine.negAddY, toAffine_addX_of_eq hPz hd]
  simp [field]

/--
@isnad1 id=eq.6h4v.s9.952662b6e96a from=seed src=0 shape=701065ee vocab=1096d5b9
-/
lemma negDblY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.negDblY P / W.dblZ P = W.toAffine.negAddY (P x / P z) (Q x / Q z) (P y / P z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [negDblY_eq hP hPz, dblZ, toAffine_slope_of_eq hPz hQz hx hy, ← (X_eq_iff hPz hQz).mp hx,
    toAffine_negAddY_of_eq hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

variable (W') in
/-- The `Y`-coordinate of a representative of `2 • P` for a projective point representative `P` on a
Weierstrass curve. -/
noncomputable def dblY (P : Fin 3 → R) : R :=
  W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

/--
@isnad1 id=eq.0h4v.s6.c5a43ccfa957 from=seed src=0 shape=94adfe35 vocab=2f81427d
-/
lemma dblY_smul (P : Fin 3 → R) (u : R) : W'.dblY (u • P) = u ^ 4 * W'.dblY P := by
  simp only [dblY, negY_eq, negDblY_smul, dblX_smul, dblZ_smul]
  ring1

/--
@isnad1 id=eq.2h3v.s6.34a847b1942d from=seed src=0 shape=8aea1279 vocab=579c5655
-/
lemma dblY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblY P = P y ^ 4 := by
  rw [dblY, negY_eq, negDblY_of_Z_eq_zero hP hPz, dblX_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz]
  ring1

/--
@isnad1 id=eq.6h4v.s9.f721102758fc from=seed src=0 shape=fea6454c vocab=ec8b3f47
-/
lemma dblY_of_Y_eq' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z)
    (hy' : P y * Q z = W'.negY Q * P z) : W'.dblY P * P z ^ 2 = eval P W'.polynomialX ^ 3 := by
  linear_combination (norm := (rw [dblY, negY_eq, dblX_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy']; ring1)) -negDblY_of_Y_eq' hP hQz hx hy hy'

/--
@isnad1 id=eq.6h4v.s8.4c1ab22f4489 from=seed src=0 shape=0ede972f vocab=813dbe5f
-/
lemma dblY_of_Y_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.dblY P = W.dblU P := by
  rw [dblU, ← dblY_of_Y_eq' hP hPz hQz hx hy hy', mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

/--
@isnad1 id=eq.6h4v.s9.7c27f620c2bd from=seed src=0 shape=701065ee vocab=df23e81c
-/
lemma dblY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.dblY P / W.dblZ P = W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  erw [dblY, negY_of_Z_ne_zero <| dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy,
    dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, negDblY_of_Z_ne_zero hP hQ hPz hQz hx hy, Affine.addY]

variable (W') in
/-- The coordinates of a representative of `2 • P` for a projective point representative `P` on a
Weierstrass curve. -/
noncomputable def dblXYZ (P : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblX P, W'.dblY P, W'.dblZ P]

/--
@isnad1 id=eq.0h3v.s5.f4b0335e28bf from=seed src=0 shape=703fff70 vocab=03ea5954
-/
lemma dblXYZ_X (P : Fin 3 → R) : W'.dblXYZ P x = W'.dblX P :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.0ebd373072a0 from=seed src=0 shape=703fff70 vocab=aa197e5c
-/
lemma dblXYZ_Y (P : Fin 3 → R) : W'.dblXYZ P y = W'.dblY P :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.ade4a1bd3d91 from=seed src=0 shape=703fff70 vocab=80fbf33e
-/
lemma dblXYZ_Z (P : Fin 3 → R) : W'.dblXYZ P z = W'.dblZ P :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.9bd6cd71495e from=seed src=0 shape=fc68f472 vocab=92f25697
-/
lemma dblXYZ_smul (P : Fin 3 → R) (u : R) : W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P := by
  rw [dblXYZ, dblX_smul, dblY_smul, dblZ_smul, smul_fin3, dblXYZ_X, dblXYZ_Y, dblXYZ_Z]

/--
@isnad1 id=eq.2h3v.s8.92bec4a146ef from=seed src=0 shape=a8b5b14f vocab=f23863b8
-/
lemma dblXYZ_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblXYZ P = P y ^ 4 • ![0, 1, 0] := by
  erw [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, smul_fin3,
    mul_zero, mul_one]

/--
@isnad1 id=eq.6h4v.s9.c2bda4e807f4 from=seed src=0 shape=e703d858 vocab=c249f9b8
-/
lemma dblXYZ_of_Y_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.dblXYZ P = W.dblU P • ![0, 1, 0] := by
  erw [dblXYZ, dblX_of_Y_eq hP hPz hQz hx hy hy', dblY_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy', smul_fin3, mul_zero, mul_one]

/--
@isnad1 id=eq.6h4v.s10.575c63bfc4ed from=seed src=0 shape=4b4167f3 vocab=4e7514cd
-/
lemma dblXYZ_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.dblXYZ P = W.dblZ P •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
  have hZ : IsUnit <| W.dblZ P := isUnit_dblZ_of_Y_ne' hP hQ hPz hQz hx hy
  erw [dblXYZ, smul_fin3, ← dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel,
    ← dblY_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel, mul_one]

/-! ## Addition formulae in projective coordinates -/

/-- The unit associated to a representative of `P + Q` for two projective point representatives `P`
and `Q` on a Weierstrass curve `W` that are not `2`-torsion.

More specifically, the unit `u` such that `W.add P Q = u • ![0, 1, 0]` where `P x / P z = Q x / Q z`
but `P ≠ W.neg P`. -/
def addU (P Q : Fin 3 → F) : F :=
  -(P y * Q z - Q y * P z) ^ 3 / (P z * Q z)

/--
@isnad1 id=eq.0h5v.s7.bdbb03e7bb49 from=seed src=0 shape=46d48605 vocab=63db8fe8
-/
lemma addU_smul (P Q : Fin 3 → F) (u v : F) : addU (u • P) (v • Q) = (u * v) ^ 2 * addU P Q := by
  simp [field, addU]

/--
@isnad1 id=eq.1h3v.s6.f6244ca3faa5 from=seed src=0 shape=b62ce368 vocab=38e95ef3
-/
lemma addU_of_Z_eq_zero_left {P Q : Fin 3 → F} (hPz : P z = 0) : addU P Q = 0 := by
  rw [addU, hPz, zero_mul, div_zero]

/--
@isnad1 id=eq.1h3v.s6.b30519bf4654 from=seed src=0 shape=8401bad9 vocab=38e95ef3
-/
lemma addU_of_Z_eq_zero_right {P Q : Fin 3 → F} (hQz : Q z = 0) : addU P Q = 0 := by
  rw [addU, hQz, mul_zero <| P z, div_zero]

/--
@isnad1 id=ne.3h3v.s7.29c0a0190aa4 from=seed src=0 shape=d133e202 vocab=24cf7308
-/
lemma addU_ne_zero_of_Y_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hy : P y * Q z ≠ Q y * P z) : addU P Q ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr <| pow_ne_zero 3 <| sub_ne_zero.mpr hy) <| mul_ne_zero hPz hQz

/--
@isnad1 id=isunit.3h3v.s7.ea9368594381 from=seed src=0 shape=cafa5198 vocab=d372030e
-/
lemma isUnit_addU_of_Y_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hy : P y * Q z ≠ Q y * P z) : IsUnit (addU P Q) :=
  (addU_ne_zero_of_Y_ne hPz hQz hy).isUnit

variable (W') in
/-- The `Z`-coordinate of a representative of `P + Q` for two distinct projective point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addZ (P Q : Fin 3 → R) : R :=
  -3 * P x ^ 2 * Q x * Q z + 3 * P x * Q x ^ 2 * P z + P y ^ 2 * Q z ^ 2 - Q y ^ 2 * P z ^ 2
    + W'.a₁ * P x * P y * Q z ^ 2 - W'.a₁ * Q x * Q y * P z ^ 2 - W'.a₂ * P x ^ 2 * Q z ^ 2
    + W'.a₂ * Q x ^ 2 * P z ^ 2 + W'.a₃ * P y * P z * Q z ^ 2 - W'.a₃ * Q y * P z ^ 2 * Q z
    - W'.a₄ * P x * P z * Q z ^ 2 + W'.a₄ * Q x * P z ^ 2 * Q z

/--
@isnad1 id=eq.2h4v.s7.7fa29af8b209 from=seed src=0 shape=939c6d05 vocab=46877f4c
-/
lemma addZ_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addZ P Q * (P z * Q z) = (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [addZ]; ring1))
    Q z ^ 3 * (equation_iff _).mp hP - P z ^ 3 * (equation_iff _).mp hQ

/--
@isnad1 id=eq.4h4v.s8.4f1c7e3514f5 from=seed src=0 shape=4e8f0cad vocab=e0aeae93
-/
lemma addZ_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) : W.addZ P Q = (P x * Q z - Q x * P z) ^ 3 / (P z * Q z) := by
  rw [← addZ_eq' hP hQ, mul_div_cancel_right₀ _ <| mul_ne_zero hPz hQz]

/--
@isnad1 id=eq.0h6v.s7.e04d6e518c67 from=seed src=0 shape=b1b4a02b vocab=cbcc9169
-/
lemma addZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addZ (u • P) (v • Q) = (u * v) ^ 2 * W'.addZ P Q := by
  simp only [addZ, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.0h3v.s5.579dcd4dbb31 from=seed src=0 shape=1c306575 vocab=72c0737d
-/
lemma addZ_self (P : Fin 3 → R) : W'.addZ P P = 0 := by
  rw [addZ]
  ring1

/--
@isnad1 id=eq.2h4v.s7.34525168a742 from=seed src=0 shape=ef2083c6 vocab=c5e50dbe
-/
lemma addZ_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addZ P Q = P y ^ 2 * Q z * Q z := by
  rw [addZ, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

/--
@isnad1 id=eq.2h4v.s7.fbb9e3b487b5 from=seed src=0 shape=322f1884 vocab=7fa3adf0
-/
lemma addZ_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addZ P Q = -(Q y ^ 2 * P z) * P z := by
  rw [addZ, hQz, X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

/--
@isnad1 id=eq.5h4v.s8.78c029e5eed6 from=seed src=0 shape=f7b6ecd6 vocab=7cd40e1a
-/
lemma addZ_of_X_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W'.addZ P Q = 0 := by
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero <| mul_ne_zero hPz hQz
  rw [addZ_eq' hP hQ, hx, sub_self, zero_pow three_ne_zero]

/--
@isnad1 id=ne.3h4v.s7.c41fec93c830 from=seed src=0 shape=f0a8de12 vocab=7cd40e1a
-/
lemma addZ_ne_zero_of_X_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z ≠ Q x * P z) : W'.addZ P Q ≠ 0 :=
  addZ_eq' hP hQ ▸ left_ne_zero_of_mul <| pow_ne_zero 3 <| sub_ne_zero.mpr hx

/--
@isnad1 id=isunit.3h4v.s7.394720490ae9 from=seed src=0 shape=4643ee4d vocab=102cf584
-/
lemma isUnit_addZ_of_X_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hx : P x * Q z ≠ Q x * P z) : IsUnit <| W.addZ P Q :=
  (addZ_ne_zero_of_X_ne hP hQ hx).isUnit

private lemma toAffine_slope_of_ne [DecidableEq F] {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ≠ Q x * P z) :
    W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z) =
      (P y * Q z - Q y * P z) / (P x * Q z - Q x * P z) := by
  simp [field, Affine.slope_of_X_ne <| by rwa [ne_eq, ← X_eq_iff hPz hQz]]

variable (W') in
/-- The `X`-coordinate of a representative of `P + Q` for two distinct projective point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addX (P Q : Fin 3 → R) : R :=
  -P x * Q y ^ 2 * P z + Q x * P y ^ 2 * Q z - 2 * P x * P y * Q y * Q z + 2 * Q x * P y * Q y * P z
    - W'.a₁ * P x ^ 2 * Q y * Q z + W'.a₁ * Q x ^ 2 * P y * P z + W'.a₂ * P x ^ 2 * Q x * Q z
    - W'.a₂ * P x * Q x ^ 2 * P z - W'.a₃ * P x * P y * Q z ^ 2 + W'.a₃ * Q x * Q y * P z ^ 2
    - 2 * W'.a₃ * P x * Q y * P z * Q z + 2 * W'.a₃ * Q x * P y * P z * Q z
    + W'.a₄ * P x ^ 2 * Q z ^ 2 - W'.a₄ * Q x ^ 2 * P z ^ 2 + 3 * W'.a₆ * P x * P z * Q z ^ 2
    - 3 * W'.a₆ * Q x * P z ^ 2 * Q z

/--
@isnad1 id=eq.2h4v.s10.a1e1950626ff from=seed src=0 shape=0cc6e777 vocab=9747218f
-/
lemma addX_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * (P z * Q z) ^ 2 =
      ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2) * (P x * Q z - Q x * P z) := by
  linear_combination (norm := (rw [addX]; ring1))
    (2 * Q x * P z * Q z ^ 3 - P x * Q z ^ 4) * (equation_iff _).mp hP
      + (Q x * P z ^ 4 - 2 * P x * P z ^ 3 * Q z) * (equation_iff _).mp hQ

/--
@isnad1 id=eq.4h4v.s10.f804f3adf307 from=seed src=0 shape=486064e8 vocab=4d3a1c68
-/
lemma addX_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) : W.addX P Q =
      ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2) * (P x * Q z - Q x * P z) / (P z * Q z) ^ 2 := by
  rw [← addX_eq' hP hQ, mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

/--
@isnad1 id=eq.0h6v.s7.962339147d31 from=seed src=0 shape=b1b4a02b vocab=bd57d252
-/
lemma addX_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addX (u • P) (v • Q) = (u * v) ^ 2 * W'.addX P Q := by
  simp only [addX, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.0h3v.s5.1cbc962c638d from=seed src=0 shape=1c306575 vocab=575fcba9
-/
lemma addX_self (P : Fin 3 → R) : W'.addX P P = 0 := by
  rw [addX]
  ring1

/--
@isnad1 id=eq.2h4v.s7.74d421ac6ffd from=seed src=0 shape=ef2083c6 vocab=06f0f286
-/
lemma addX_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addX P Q = P y ^ 2 * Q z * Q x := by
  rw [addX, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

/--
@isnad1 id=eq.2h4v.s7.1e46ac654589 from=seed src=0 shape=322f1884 vocab=35a64275
-/
lemma addX_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addX P Q = -(Q y ^ 2 * P z) * P x := by
  rw [addX, hQz, X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

/--
@isnad1 id=eq.5h4v.s8.a554a745f1cb from=seed src=0 shape=f7b6ecd6 vocab=8a744ceb
-/
lemma addX_of_X_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W'.addX P Q = 0 := by
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero <| pow_ne_zero 2 <| mul_ne_zero hPz hQz
  rw [addX_eq' hP hQ, hx]
  ring1

private lemma toAffine_addX_of_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {n d : F}
    (hd : d ≠ 0) : W.toAffine.addX (P x / P z) (Q x / Q z) (n / d) =
      (n ^ 2 * P z * Q z + W.a₁ * n * P z * Q z * d - W.a₂ * P z * Q z * d ^ 2 - P x * Q z * d ^ 2
        - Q x * P z * d ^ 2) * d / (P z * Q z) ^ 2 / (d ^ 3 / (P z * Q z)) := by
  simp [field]

/--
@isnad1 id=eq.5h4v.s9.b239a620bd6c from=seed src=0 shape=e936b55b vocab=20f55571
-/
lemma addX_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.addX P Q / W.addZ P Q =
    W.toAffine.addX (P x / P z) (Q x / Q z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [addX_eq hP hQ hPz hQz, addZ_eq hP hQ hPz hQz, toAffine_slope_of_ne hPz hQz hx,
    toAffine_addX_of_ne hPz hQz <| sub_ne_zero.mpr hx]

variable (W') in
/-- The `Y`-coordinate of a representative of `-(P + Q)` for two distinct projective point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def negAddY (P Q : Fin 3 → R) : R :=
  -3 * P x ^ 2 * Q x * Q y + 3 * P x * Q x ^ 2 * P y - P y ^ 2 * Q y * Q z + P y * Q y ^ 2 * P z
    + W'.a₁ * P x * Q y ^ 2 * P z - W'.a₁ * Q x * P y ^ 2 * Q z - W'.a₂ * P x ^ 2 * Q y * Q z
    + W'.a₂ * Q x ^ 2 * P y * P z + 2 * W'.a₂ * P x * Q x * P y * Q z
    - 2 * W'.a₂ * P x * Q x * Q y * P z - W'.a₃ * P y ^ 2 * Q z ^ 2 + W'.a₃ * Q y ^ 2 * P z ^ 2
    + W'.a₄ * P x * P y * Q z ^ 2 - 2 * W'.a₄ * P x * Q y * P z * Q z
    + 2 * W'.a₄ * Q x * P y * P z * Q z - W'.a₄ * Q x * Q y * P z ^ 2
    + 3 * W'.a₆ * P y * P z * Q z ^ 2 - 3 * W'.a₆ * Q y * P z ^ 2 * Q z

/--
@isnad1 id=eq.2h4v.s10.b0b63494d87b from=seed src=0 shape=9e17fec1 vocab=854504c8
-/
lemma negAddY_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.negAddY P Q * (P z * Q z) ^ 2 =
      (P y * Q z - Q y * P z) * ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2)
        + P y * Q z * (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [negAddY]; ring1))
    (2 * Q y * P z * Q z ^ 3 - P y * Q z ^ 4) * (equation_iff _).mp hP
      + (Q y * P z ^ 4 - 2 * P y * P z ^ 3 * Q z) * (equation_iff _).mp hQ

/--
@isnad1 id=eq.4h4v.s11.03a02cecde3b from=seed src=0 shape=0346e46a vocab=05a6c7ea
-/
lemma negAddY_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) : W.negAddY P Q =
      ((P y * Q z - Q y * P z) * ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2)
        + P y * Q z * (P x * Q z - Q x * P z) ^ 3) / (P z * Q z) ^ 2 := by
  rw [← negAddY_eq' hP hQ, mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

/--
@isnad1 id=eq.0h6v.s7.adb15efb2886 from=seed src=0 shape=b1b4a02b vocab=acd58581
-/
lemma negAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.negAddY (u • P) (v • Q) = (u * v) ^ 2 * W'.negAddY P Q := by
  simp only [negAddY, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.0h3v.s5.14ceb716aca3 from=seed src=0 shape=1c306575 vocab=72726844
-/
lemma negAddY_self (P : Fin 3 → R) : W'.negAddY P P = 0 := by
  rw [negAddY]
  ring1

/--
@isnad1 id=eq.2h4v.s7.99c33bc60c33 from=seed src=0 shape=a8687b0b vocab=564b1286
-/
lemma negAddY_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.negAddY P Q = P y ^ 2 * Q z * W'.negY Q := by
  rw [negAddY, hPz, X_eq_zero_of_Z_eq_zero hP hPz, negY]
  ring1

/--
@isnad1 id=eq.2h4v.s7.9e9e27d3027b from=seed src=0 shape=35c2a5d8 vocab=a696c680
-/
lemma negAddY_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.negAddY P Q = -(Q y ^ 2 * P z) * W'.negY P := by
  rw [negAddY, hQz, X_eq_zero_of_Z_eq_zero hQ hQz, negY]
  ring1

/--
@isnad1 id=eq.3h4v.s8.79cabde12399 from=seed src=0 shape=e795549a vocab=a20dc1eb
-/
lemma negAddY_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z = Q x * P z) :
    W'.negAddY P Q * (P z * Q z) ^ 2 = (P y * Q z - Q y * P z) ^ 3 * (P z * Q z) := by
  rw [negAddY_eq' hP hQ, hx]
  ring1

/--
@isnad1 id=eq.5h4v.s8.25a777dd97f6 from=seed src=0 shape=34865689 vocab=abc13fe6
-/
lemma negAddY_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W.negAddY P Q = -addU P Q := by
  rw [addU, neg_div, neg_neg, ← mul_div_mul_right _ _ <| mul_ne_zero hPz hQz,
    ← negAddY_of_X_eq' hP hQ hx, ← sq,
    mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

private lemma toAffine_negAddY_of_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {n d : F}
    (hd : d ≠ 0) : W.toAffine.negAddY (P x / P z) (Q x / Q z) (P y / P z) (n / d) =
      (n * (n ^ 2 * P z * Q z + W.a₁ * n * P z * Q z * d - W.a₂ * P z * Q z * d ^ 2
        - P x * Q z * d ^ 2 - Q x * P z * d ^ 2 - P x * Q z * d ^ 2) + P y * Q z * d ^ 3)
        / (P z * Q z) ^ 2 / (d ^ 3 / (P z * Q z)) := by
  rw [Affine.negAddY, toAffine_addX_of_ne hPz hQz hd]
  simp [field]

/--
@isnad1 id=eq.5h4v.s9.19f0b32ddede from=seed src=0 shape=a78b976a vocab=d5295850
-/
lemma negAddY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.negAddY P Q / W.addZ P Q =
      W.toAffine.negAddY (P x / P z) (Q x / Q z) (P y / P z)
        (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [negAddY_eq hP hQ hPz hQz, addZ_eq hP hQ hPz hQz, toAffine_slope_of_ne hPz hQz hx,
    toAffine_negAddY_of_ne hPz hQz <| sub_ne_zero.mpr hx]

variable (W') in
/-- The `Y`-coordinate of a representative of `P + Q` for two distinct projective point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addY (P Q : Fin 3 → R) : R :=
  W'.negY ![W'.addX P Q, W'.negAddY P Q, W'.addZ P Q]

/--
@isnad1 id=eq.0h6v.s7.dd1ffe9c230c from=seed src=0 shape=b1b4a02b vocab=b5870d9c
-/
lemma addY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addY (u • P) (v • Q) = (u * v) ^ 2 * W'.addY P Q := by
  simp only [addY, negY_eq, negAddY_smul, addX_smul, addZ_smul]
  ring1

/--
@isnad1 id=eq.0h3v.s5.ac5cc652ee86 from=seed src=0 shape=1c306575 vocab=08cb9898
-/
lemma addY_self (P : Fin 3 → R) : W'.addY P P = 0 := by
  simp only [addY, negY_eq, negAddY_self, addX_self, addZ_self, neg_zero, mul_zero, sub_zero]

/--
@isnad1 id=eq.2h4v.s7.f9b347d4e33f from=seed src=0 shape=ef2083c6 vocab=6f4e6386
-/
lemma addY_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addY P Q = P y ^ 2 * Q z * Q y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_left hP hPz, negY, addX_of_Z_eq_zero_left hP hPz,
    addZ_of_Z_eq_zero_left hP hPz]
  ring1

/--
@isnad1 id=eq.2h4v.s7.23269e4c3887 from=seed src=0 shape=322f1884 vocab=ce808348
-/
lemma addY_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addY P Q = -(Q y ^ 2 * P z) * P y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_right hQ hQz, negY, addX_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQ hQz]
  ring1

/--
@isnad1 id=eq.5h4v.s9.bd7cbd868985 from=seed src=0 shape=ab01f0cc vocab=9d36fc92
-/
lemma addY_of_X_eq' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) :
    W'.addY P Q * (P z * Q z) ^ 3 = -(P y * Q z - Q y * P z) ^ 3 * (P z * Q z) ^ 2 := by
  linear_combination (norm := (rw [addY, negY_eq, addX_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx]; ring1)) -(P z * Q z) * negAddY_of_X_eq' hP hQ hx

/--
@isnad1 id=eq.5h4v.s7.f9a893116208 from=seed src=0 shape=878256e8 vocab=d34d085e
-/
lemma addY_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W.addY P Q = addU P Q := by
  rw [addU, ← mul_div_mul_right _ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz,
    ← addY_of_X_eq' hP hQ hPz hQz hx, ← pow_succ',
    mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

/--
@isnad1 id=eq.5h4v.s9.49d5f82dcaa5 from=seed src=0 shape=a78b976a vocab=6a8cb9ed
-/
lemma addY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.addY P Q / W.addZ P Q =
      W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
        (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  erw [addY, negY_of_Z_ne_zero <| addZ_ne_zero_of_X_ne hP hQ hx, addX_of_Z_ne_zero hP hQ hPz hQz hx,
    negAddY_of_Z_ne_zero hP hQ hPz hQz hx, Affine.addY]

variable (W') in
/-- The coordinates of a representative of `P + Q` for two distinct projective point representatives
`P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `![0, 0, 0]`. -/
noncomputable def addXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.addX P Q, W'.addY P Q, W'.addZ P Q]

/--
@isnad1 id=eq.0h4v.s5.8e5d249832e7 from=seed src=0 shape=7edeb210 vocab=eae5f9ab
-/
lemma addXYZ_X (P Q : Fin 3 → R) : W'.addXYZ P Q x = W'.addX P Q :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.f37d6ba10e85 from=seed src=0 shape=7edeb210 vocab=3400bd86
-/
lemma addXYZ_Y (P Q : Fin 3 → R) : W'.addXYZ P Q y = W'.addY P Q :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.716de616cccb from=seed src=0 shape=7edeb210 vocab=104866d1
-/
lemma addXYZ_Z (P Q : Fin 3 → R) : W'.addXYZ P Q z = W'.addZ P Q :=
  rfl

/--
@isnad1 id=eq.0h6v.s7.babacc8f837d from=seed src=0 shape=70df6811 vocab=ed38142c
-/
lemma addXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q := by
  rw [addXYZ, addX_smul, addY_smul, addZ_smul, smul_fin3, addXYZ_X, addXYZ_Y, addXYZ_Z]

/--
@isnad1 id=eq.0h3v.s6.da35b821ef55 from=seed src=0 shape=30a36d22 vocab=48021185
-/
lemma addXYZ_self (P : Fin 3 → R) : W'.addXYZ P P = ![0, 0, 0] := by
  rw [addXYZ, addX_self, addY_self, addZ_self]

/--
@isnad1 id=eq.2h4v.s7.e744e34ec92b from=seed src=0 shape=f6b5589b vocab=fb4d48c6
-/
lemma addXYZ_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addXYZ P Q = (P y ^ 2 * Q z) • Q := by
  rw [addXYZ, addX_of_Z_eq_zero_left hP hPz, addY_of_Z_eq_zero_left hP hPz,
    addZ_of_Z_eq_zero_left hP hPz, smul_fin3]

/--
@isnad1 id=eq.2h4v.s7.76817498859e from=seed src=0 shape=e222bf67 vocab=617f47b5
-/
lemma addXYZ_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addXYZ P Q = -(Q y ^ 2 * P z) • P := by
  rw [addXYZ, addX_of_Z_eq_zero_right hQ hQz, addY_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQ hQz, smul_fin3]

/--
@isnad1 id=eq.5h4v.s8.bc7325916ece from=seed src=0 shape=bb6c1648 vocab=a0d3ef2b
-/
lemma addXYZ_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W.addXYZ P Q = addU P Q • ![0, 1, 0] := by
  erw [addXYZ, addX_of_X_eq hP hQ hPz hQz hx, addY_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx, smul_fin3, mul_zero, mul_one]

/--
@isnad1 id=eq.5h4v.s10.c775678b8b81 from=seed src=0 shape=4696396e vocab=1fad992a
-/
lemma addXYZ_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.addXYZ P Q = W.addZ P Q •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
  have hZ : IsUnit <| W.addZ P Q := isUnit_addZ_of_X_ne hP hQ hx
  erw [addXYZ, smul_fin3, ← addX_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel,
    ← addY_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel, mul_one]

/-! ## Maps and base changes -/

variable (f : R →+* S) (P Q : Fin 3 → R)

/--
@isnad1 id=eq.0h5v.s7.4329b749f6b9 from=seed src=0 shape=92bdc66f vocab=58e5253a
-/
@[simp]
lemma map_negY : (W'.map f).negY (f ∘ P) = f (W'.negY P) := by
  simp only [negY]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.f289f6cbdf3f from=seed src=0 shape=92bdc66f vocab=01a74a35
-/
@[simp]
lemma map_dblU (f : F →+* K) (P : Fin 3 → F) : (W.map f).dblU (f ∘ P) = f (W.dblU P) := by
  simp only [dblU_eq]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.4002fc9dae29 from=seed src=0 shape=92bdc66f vocab=45177391
-/
@[simp]
lemma map_dblZ : (W'.map f).dblZ (f ∘ P) = f (W'.dblZ P) := by
  simp only [dblZ, negY]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.c5c3e7bd1975 from=seed src=0 shape=92bdc66f vocab=dfab705b
-/
@[simp]
lemma map_dblX : (W'.map f).dblX (f ∘ P) = f (W'.dblX P) := by
  simp only [dblX]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.726671bfcffe from=seed src=0 shape=92bdc66f vocab=8fcb46be
-/
@[simp]
lemma map_negDblY : (W'.map f).negDblY (f ∘ P) = f (W'.negDblY P) := by
  simp only [negDblY]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.6d24fe8eefd0 from=seed src=0 shape=92bdc66f vocab=ab511bf9
-/
@[simp]
lemma map_dblY : (W'.map f).dblY (f ∘ P) = f (W'.dblY P) := by
  simp only [dblY, negY_eq, map_negDblY, map_dblX, map_dblZ]
  map_simp

/--
@isnad1 id=eq.0h5v.s7.7cd879e760bf from=seed src=0 shape=63cb483b vocab=e20fec46
-/
@[simp]
lemma map_dblXYZ : (W'.map f).dblXYZ (f ∘ P) = f ∘ dblXYZ W' P := by
  simp only [dblXYZ, map_dblX, map_dblY, map_dblZ, comp_fin3]

/--
@isnad1 id=eq.0h5v.s7.49d66a88a1fb from=seed src=0 shape=deeb099f vocab=dad214ec
-/
@[simp]
lemma map_addU (f : F →+* K) (P Q : Fin 3 → F) : addU (f ∘ P) (f ∘ Q) = f (addU P Q) := by
  simp only [addU]
  map_simp

/--
@isnad1 id=eq.0h6v.s7.d27b47437dc3 from=seed src=0 shape=a2e09276 vocab=06a9495d
-/
@[simp]
lemma map_addZ : (W'.map f).addZ (f ∘ P) (f ∘ Q) = f (W'.addZ P Q) := by
  simp only [addZ]
  map_simp

/--
@isnad1 id=eq.0h6v.s7.8ff9edd7ccc9 from=seed src=0 shape=a2e09276 vocab=a7726a86
-/
@[simp]
lemma map_addX : (W'.map f).addX (f ∘ P) (f ∘ Q) = f (W'.addX P Q) := by
  simp only [addX]
  map_simp

/--
@isnad1 id=eq.0h6v.s7.63c539348f2b from=seed src=0 shape=a2e09276 vocab=c93cd43f
-/
@[simp]
lemma map_negAddY : (W'.map f).negAddY (f ∘ P) (f ∘ Q) = f (W'.negAddY P Q) := by
  simp only [negAddY]
  map_simp

/--
@isnad1 id=eq.0h6v.s7.6f28fa43f9f3 from=seed src=0 shape=a2e09276 vocab=29fe1cae
-/
@[simp]
lemma map_addY : (W'.map f).addY (f ∘ P) (f ∘ Q) = f (W'.addY P Q) := by
  simp only [addY, negY_eq, map_negAddY, map_addX, map_addZ]
  map_simp

/--
@isnad1 id=eq.0h6v.s7.092757b2bc63 from=seed src=0 shape=4f98816f vocab=431d3528
-/
@[simp]
lemma map_addXYZ : (W'.map f).addXYZ (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q := by
  simp only [addXYZ, map_addX, map_addY, map_addZ, comp_fin3]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B) (P Q : Fin 3 → A)

/--
@isnad1 id=eq.0h7v.s8.3ad7a0392be6 from=seed src=0 shape=5bc7e8cb vocab=b43513db
-/
lemma baseChange_negY : (W'⁄B).negY (f ∘ P) = f ((W'⁄A).negY P) := by
  rw [← RingHom.coe_coe, ← map_negY, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.7cab4270290c from=seed src=0 shape=51236f31 vocab=e5052c77
-/
lemma baseChange_dblU [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K] (f : F →ₐ[S] K) (P : Fin 3 → F) :
    (W'⁄K).dblU (f ∘ P) = f ((W'⁄F).dblU P) := by
  rw [← RingHom.coe_coe, ← map_dblU, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.8a0c8635f826 from=seed src=0 shape=5bc7e8cb vocab=96d70149
-/
lemma baseChange_dblZ : (W'⁄B).dblZ (f ∘ P) = f ((W'⁄A).dblZ P) := by
  rw [← RingHom.coe_coe, ← map_dblZ, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.11bbfa867b8b from=seed src=0 shape=5bc7e8cb vocab=f52faeff
-/
lemma baseChange_dblX : (W'⁄B).dblX (f ∘ P) = f ((W'⁄A).dblX P) := by
  rw [← RingHom.coe_coe, ← map_dblX, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.358934aaf12c from=seed src=0 shape=5bc7e8cb vocab=f2d2fe1c
-/
lemma baseChange_negDblY : (W'⁄B).negDblY (f ∘ P) = f ((W'⁄A).negDblY P) := by
  rw [← RingHom.coe_coe, ← map_negDblY, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.321d616d9161 from=seed src=0 shape=5bc7e8cb vocab=38931830
-/
lemma baseChange_dblY : (W'⁄B).dblY (f ∘ P) = f ((W'⁄A).dblY P) := by
  rw [← RingHom.coe_coe, ← map_dblY, map_baseChange]

/--
@isnad1 id=eq.0h7v.s8.2573bb73730d from=seed src=0 shape=a29f2889 vocab=6f826c3e
-/
lemma baseChange_dblXYZ : (W'⁄B).dblXYZ (f ∘ P) = f ∘ (W'⁄A).dblXYZ P := by
  rw [← RingHom.coe_coe, ← map_dblXYZ, map_baseChange]

/--
@isnad1 id=eq.0h8v.s8.2925fff0891b from=seed src=0 shape=ea2a2746 vocab=a40c30c3
-/
lemma baseChange_addX : (W'⁄B).addX (f ∘ P) (f ∘ Q) = f ((W'⁄A).addX P Q) := by
  rw [← RingHom.coe_coe, ← map_addX, map_baseChange]

/--
@isnad1 id=eq.0h8v.s8.7d8a4e3ee7a0 from=seed src=0 shape=ea2a2746 vocab=105457a3
-/
lemma baseChange_negAddY : (W'⁄B).negAddY (f ∘ P) (f ∘ Q) = f ((W'⁄A).negAddY P Q) := by
  rw [← RingHom.coe_coe, ← map_negAddY, map_baseChange]

/--
@isnad1 id=eq.0h8v.s8.c3753e303a8d from=seed src=0 shape=ea2a2746 vocab=bcb52a87
-/
lemma baseChange_addY : (W'⁄B).addY (f ∘ P) (f ∘ Q) = f ((W'⁄A).addY P Q) := by
  rw [← RingHom.coe_coe, ← map_addY, map_baseChange]

/--
@isnad1 id=eq.0h8v.s8.87e46b397219 from=seed src=0 shape=25e54fc1 vocab=59e3fcab
-/
lemma baseChange_addXYZ : (W'⁄B).addXYZ (f ∘ P) (f ∘ Q) = f ∘ (W'⁄A).addXYZ P Q := by
  rw [← RingHom.coe_coe, ← map_addXYZ, map_baseChange]

end Projective

end WeierstrassCurve
