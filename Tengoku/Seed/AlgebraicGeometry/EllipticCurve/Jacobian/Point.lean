/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Jacobian.Formula

/-!
# Nonsingular points and the group law in Jacobian coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular Jacobian points of `W` can be
endowed with a group law, which is uniquely determined by the formulae in
`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean` and follows from an equivalence with
the nonsingular points in affine coordinates.

This file defines the group law on nonsingular Jacobian points.

## Main definitions

* `WeierstrassCurve.Jacobian.neg`: the negation of a point representative.
* `WeierstrassCurve.Jacobian.negMap`: the negation of a point class.
* `WeierstrassCurve.Jacobian.add`: the addition of two point representatives.
* `WeierstrassCurve.Jacobian.addMap`: the addition of two point classes.
* `WeierstrassCurve.Jacobian.Point`: a nonsingular Jacobian point.
* `WeierstrassCurve.Jacobian.Point.neg`: the negation of a nonsingular Jacobian point.
* `WeierstrassCurve.Jacobian.Point.add`: the addition of two nonsingular Jacobian points.
* `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`: the equivalence between the type of
  nonsingular Jacobian points with the type of nonsingular points in affine coordinates.

## Main statements

* `WeierstrassCurve.Jacobian.nonsingular_neg`: negation preserves the nonsingular condition.
* `WeierstrassCurve.Jacobian.nonsingular_add`: addition preserves the nonsingular condition.
* `WeierstrassCurve.Jacobian.Point.instAddCommGroup`: the type of nonsingular Jacobian points forms
  an abelian group under addition.

## Implementation notes

Note that `W(X, Y, Z)` and its partial derivatives are independent of the point representative, and
the nonsingularity condition already implies `(x, y, z) ≠ (0, 0, 0)`, so a nonsingular Jacobian
point on `W` can be given by `[x : y : z]` and the nonsingular condition on any representative.

A nonsingular Jacobian point representative can be converted to a nonsingular point in affine
coordinates using `WeierstrassCurve.Jacobian.Point.toAffine`, which lifts to a map on nonsingular
Jacobian points using `WeierstrassCurve.Jacobian.Point.toAffineLift`. Conversely, a nonsingular
point in affine coordinates can be converted to a nonsingular Jacobian point using
`WeierstrassCurve.Jacobian.Point.fromAffine` or `WeierstrassCurve.Affine.Point.toJacobian`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, point, group law
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

/-! ## Negation on Jacobian point representatives -/

variable (W') in
/-- The negation of a Jacobian point representative on a Weierstrass curve. -/
def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, W'.negY P, P z]

/--
@isnad1 id=eq.0h3v.s5.2b2ee8d50c2e from=seed src=0 shape=92a61ede vocab=eaf93038
-/
lemma neg_X (P : Fin 3 → R) : W'.neg P x = P x :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.279770807977 from=seed src=0 shape=703fff70 vocab=1fd0dbf9
-/
lemma neg_Y (P : Fin 3 → R) : W'.neg P y = W'.negY P :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.e46204a98c1c from=seed src=0 shape=92a61ede vocab=eaf93038
-/
lemma neg_Z (P : Fin 3 → R) : W'.neg P z = P z :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.3b4884bbd537 from=seed src=0 shape=eb1ac6f9 vocab=69abcc65
-/
protected lemma neg_smul (P : Fin 3 → R) (u : R) : W'.neg (u • P) = u • W'.neg P := by
  rw [neg, negY_smul]
  rfl

/--
@isnad1 id=equiv.1h4v.s6.61f63483cb99 from=seed src=0 shape=27565bfe vocab=dadf9752
-/
lemma neg_smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P :=
  ⟨hu.unit, (W'.neg_smul ..).symm⟩

/--
@isnad1 id=equiv.0h5v.s6.8b24a633c84d from=seed src=0 shape=0c4360c8 vocab=de0ab665
-/
lemma neg_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.neg P ≈ W'.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit

/--
@isnad1 id=eq.1h3v.s7.47b3d6a27802 from=seed src=0 shape=90e952d5 vocab=eb9406c5
-/
lemma neg_of_Z_eq_zero' {P : Fin 3 → R} (hPz : P z = 0) : W'.neg P = ![P x, -P y, 0] := by
  rw [neg, negY_of_Z_eq_zero hPz, hPz]

/--
@isnad1 id=eq.2h3v.s8.155e64e0b24d from=seed src=0 shape=69164a2d vocab=256cbc64
-/
lemma neg_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.neg P = -(P y / P x) • ![1, 1, 0] := by
  have hX {n : ℕ} : IsUnit <| P x ^ n := (isUnit_X_of_Z_eq_zero hP hPz).pow n
  erw [neg_of_Z_eq_zero' hPz, smul_fin3, neg_sq, div_pow, (equation_of_Z_eq_zero hPz).mp hP.left,
    pow_succ, hX.mul_div_cancel_left, mul_one, Odd.neg_pow <| by decide, div_pow, pow_succ,
    (equation_of_Z_eq_zero hPz).mp hP.left, hX.mul_div_cancel_left, mul_one, mul_zero]

/--
@isnad1 id=eq.1h3v.s8.50aeb5a44866 from=seed src=0 shape=e8f2069e vocab=b962b792
-/
lemma neg_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.neg P = P z • ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] := by
  rw [neg, smul_fin3]
  simp only [fin3_def_ext]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hPz, ← negY_of_Z_ne_zero hPz,
    mul_div_cancel₀ _ <| pow_ne_zero 3 hPz, mul_one]

private lemma nonsingular_neg_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    W.Nonsingular ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] :=
  (nonsingular_some ..).mpr <| (Affine.nonsingular_neg ..).mpr <|
    (nonsingular_of_Z_ne_zero hPz).mp hP

/--
@isnad1 id=nonsingu.1h3v.s5.e103480ede74 from=seed src=0 shape=1d875cbd vocab=09d2205c
-/
lemma nonsingular_neg {P : Fin 3 → F} (hP : W.Nonsingular P) : W.Nonsingular <| W.neg P := by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP hPz, nonsingular_smul _
        ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg, nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]

/--
@isnad1 id=eq.0h3v.s5.330063011919 from=seed src=0 shape=5c6a9355 vocab=deecde25
-/
lemma addZ_neg (P : Fin 3 → R) : addZ P (W'.neg P) = 0 :=
  addZ_of_X_eq rfl

/--
@isnad1 id=eq.1h3v.s5.2dbe5b115308 from=seed src=0 shape=4f19658e vocab=fb1eef39
-/
lemma addX_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addX P (W'.neg P) = W'.dblZ P ^ 2 := by
  linear_combination (norm := (rw [addX, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 2 * (equation_iff _).mp hP

/--
@isnad1 id=eq.1h3v.s5.5a097953b782 from=seed src=0 shape=4f19658e vocab=c9e69529
-/
lemma negAddY_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.negAddY P (W'.neg P) = W'.dblZ P ^ 3 := by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 3 * (P y - W'.negY P) * (equation_iff _).mp hP

/--
@isnad1 id=eq.1h3v.s6.03a2aac8fe8a from=seed src=0 shape=fc3c38c0 vocab=522be5ed
-/
lemma addY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W'.dblZ P ^ 3 := by
  rw [addY, addX_neg hP, negAddY_neg hP, addZ_neg, negY_of_Z_eq_zero rfl]
  rfl

/--
@isnad1 id=eq.1h3v.s7.c84ab8579049 from=seed src=0 shape=35cb823f vocab=71ca9eec
-/
lemma addXYZ_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.addXYZ P (W'.neg P) = -W'.dblZ P • ![1, 1, 0] := by
  rw [addXYZ, addX_neg hP, addY_neg hP, addZ_neg, smul_fin3]
  simp +decide [fin3_def_ext, Odd.neg_pow]

variable (W') in
/-- The negation of a Jacobian point class on a Weierstrass curve `W`.

If `P` is a Jacobian point representative on `W`, then `W.negMap ⟦P⟧` is definitionally equivalent
to `W.neg P`. -/
def negMap (P : PointClass R) : PointClass R :=
  P.map W'.neg fun _ _ => neg_equiv

/--
@isnad1 id=eq.0h3v.s7.6cc051a96468 from=seed src=0 shape=a2c7359d vocab=7c444f21
-/
lemma negMap_eq (P : Fin 3 → R) : W'.negMap ⟦P⟧ = ⟦W'.neg P⟧ :=
  rfl

/--
@isnad1 id=eq.2h3v.s8.8a415ea1dde1 from=seed src=0 shape=4dbbadce vocab=18578131
-/
lemma negMap_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![1, 1, 0]⟧ := by
  rw [negMap_eq, neg_of_Z_eq_zero hP hPz,
    smul_eq _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg]

/--
@isnad1 id=eq.1h3v.s8.a9d2455dfeed from=seed src=0 shape=4ba650e3 vocab=d5ca0316
-/
lemma negMap_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negMap ⟦P⟧ = ⟦![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1]⟧ := by
  rw [negMap_eq, neg_of_Z_ne_zero hPz, smul_eq _ <| Ne.isUnit hPz]

/--
@isnad1 id=nonsingu.1h3v.s5.99ab08e249b2 from=seed src=0 shape=c8b2c16d vocab=702f0e15
-/
lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
    W.NonsingularLift <| W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

/-! ## Addition on Jacobian point representatives -/

open scoped Classical in
variable (W') in
/-- The addition of two Jacobian point representatives on a Weierstrass curve. -/
noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q

/--
@isnad1 id=eq.0h5v.s6.3cfe48687b82 from=seed src=0 shape=80e8c2f9 vocab=93f7f5ce
-/
lemma add_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.add P Q = W'.dblXYZ P :=
  ite_eq_left h

/--
@isnad1 id=eq.2h7v.s7.64f7261f3fb9 from=seed src=0 shape=b37687a2 vocab=0421e571
-/
lemma add_smul_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) = u ^ 4 • W'.add P Q := by
  rw [add_of_equiv <| (smul_equiv_smul P Q hu hv).mpr h, dblXYZ_smul, add_of_equiv h]

/--
@isnad1 id=eq.0h3v.s5.82883cb660f1 from=seed src=0 shape=70894a8f vocab=9732fc38
-/
lemma add_self (P : Fin 3 → R) : W'.add P P = W'.dblXYZ P :=
  add_of_equiv <| Setoid.refl _

/--
@isnad1 id=eq.1h4v.s5.799191f1ff45 from=seed src=0 shape=6c0ae8c0 vocab=9732fc38
-/
lemma add_of_eq {P Q : Fin 3 → R} (h : P = Q) : W'.add P Q = W'.dblXYZ P :=
  h ▸ add_self P

/--
@isnad1 id=eq.1h4v.s6.8e55c11bbc75 from=seed src=0 shape=995cfb39 vocab=0c05bbc1
-/
lemma add_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q :=
  ite_eq_right h

/--
@isnad1 id=eq.3h6v.s7.31e90b5429b8 from=seed src=0 shape=62afc489 vocab=c5d29db5
-/
lemma add_smul_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u)
    (hv : IsUnit v) : W'.add (u • P) (v • Q) = (u * v) ^ 2 • W'.add P Q := by
  rw [add_of_not_equiv <| h.comp (smul_equiv_smul P Q hu hv).mp, addXYZ_smul, add_of_not_equiv h]

/--
@isnad1 id=equiv.2h6v.s7.d6128ebf3503 from=seed src=0 shape=220ef025 vocab=27d19353
-/
lemma add_smul_equiv (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) ≈ W'.add P Q := by
  by_cases h : P ≈ Q
  · exact ⟨hu.unit ^ 4, by convert! (add_smul_of_equiv h hu hv).symm⟩
  · exact ⟨(hu.unit * hv.unit) ^ 2, by convert! (add_smul_of_not_equiv h hu hv).symm⟩

/--
@isnad1 id=equiv.0h8v.s6.ca594d16283e from=seed src=0 shape=c15fea32 vocab=6d83f55b
-/
lemma add_equiv {P P' Q Q' : Fin 3 → R} (hP : P ≈ P') (hQ : Q ≈ Q') :
    W'.add P Q ≈ W'.add P' Q' := by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u.isUnit v.isUnit

/--
@isnad1 id=eq.4h4v.s8.6e1b95ae716a from=seed src=0 shape=a15432d4 vocab=6703e48c
-/
lemma add_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : W.add P Q = P x ^ 2 • ![1, 1, 0] := by
  rw [add_of_equiv <| equiv_of_Z_eq_zero hP hQ hPz hQz, dblXYZ_of_Z_eq_zero hP.left hPz]

/--
@isnad1 id=eq.3h4v.s7.0efc41ac222a from=seed src=0 shape=e6d9eb2e vocab=3c13ed23
-/
lemma add_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) (hQz : Q z ≠ 0) :
    W'.add P Q = (P x * Q z) • Q := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_left hPz hQz, addXYZ_of_Z_eq_zero_left hP hPz]

/--
@isnad1 id=eq.3h4v.s7.af27477a2d54 from=seed src=0 shape=d715f25c vocab=c31c0cf1
-/
lemma add_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z = 0) : W'.add P Q = -(Q x * P z) • P := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_right hPz hQz, addXYZ_of_Z_eq_zero_right hQ hQz]

/--
@isnad1 id=eq.5h4v.s9.c44f1afdd9ef from=seed src=0 shape=ee3c80dc vocab=a5f8314e
-/
lemma add_of_Y_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.add P Q = W.dblU P • ![1, 1, 0] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx hy, dblXYZ_of_Y_eq hQz hx hy hy']

/--
@isnad1 id=eq.6h4v.s9.bc35206d479f from=seed src=0 shape=77c48b01 vocab=025d1483
-/
lemma add_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    W.add P Q = addU P Q • ![1, 1, 0] := by
  rw [add_of_not_equiv <| not_equiv_of_Y_ne hy, addXYZ_of_X_eq hP hQ hPz hQz hx]

/--
@isnad1 id=eq.6h4v.s10.9153f7310c10 from=seed src=0 shape=10285c7f vocab=b8cc5edc
-/
lemma add_of_Y_ne' [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.add P Q = W.dblZ P •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx <| Y_eq_of_Y_ne' hP hQ hx hy,
    dblXYZ_of_Z_ne_zero hP hQ hPz hQz hx hy]

/--
@isnad1 id=eq.5h4v.s10.0ec91a987ffb from=seed src=0 shape=57d8c3d8 vocab=51a47519
-/
lemma add_of_X_ne [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : W.add P Q = addZ P Q •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  rw [add_of_not_equiv <| not_equiv_of_X_ne hx, addXYZ_of_Z_ne_zero hP hQ hPz hQz hx]

private lemma nonsingular_add_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) : W.Nonsingular
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)), 1] :=
  (nonsingular_some ..).mpr <| Affine.nonsingular_add ((nonsingular_of_Z_ne_zero hPz).mp hP)
    ((nonsingular_of_Z_ne_zero hQz).mp hQ) <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]

/--
@isnad1 id=nonsingu.2h4v.s5.aede53b9899c from=seed src=0 shape=a8334ee2 vocab=587f1f61
-/
lemma nonsingular_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Nonsingular <| W.add P Q := by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz,
        nonsingular_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
        nonsingular_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · simp only [add_of_Y_eq hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            nonsingular_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · classical
        have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            nonsingular_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx <| not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
            nonsingular_smul _ <| isUnit_addZ_of_X_ne hx]

variable (W') in
/-- The addition of two Jacobian point classes on a Weierstrass curve `W`.

If `P` and `Q` are two Jacobian point representatives on `W`, then `W.addMap ⟦P⟧ ⟦Q⟧` is
definitionally equivalent to `W.add P Q`. -/
noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

/--
@isnad1 id=eq.0h4v.s7.67ec1e167461 from=seed src=0 shape=c13e2c50 vocab=466a6bef
-/
lemma addMap_eq (P Q : Fin 3 → R) : W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧ :=
  rfl

/--
@isnad1 id=eq.3h4v.s7.7488a2249f1d from=seed src=0 shape=9e4a260b vocab=7178610e
-/
lemma addMap_of_Z_eq_zero_left {P : Fin 3 → F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  revert hQ
  refine Q.inductionOn (motive := fun Q => _ → W.addMap _ Q = Q) fun Q hQ => ?_
  by_cases hQz : Q z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hQ hQz
  · rw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]

/--
@isnad1 id=eq.3h4v.s7.5fcc64c5f60e from=seed src=0 shape=a15afd33 vocab=7178610e
-/
lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 → F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  revert hP
  refine P.inductionOn (motive := fun P => _ → W.addMap P _ = P) fun P hP => ?_
  by_cases hPz : P z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
  · rw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]

/--
@isnad1 id=eq.6h4v.s9.a3c016268c3c from=seed src=0 shape=37524fe5 vocab=898fbef6
-/
lemma addMap_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.addMap ⟦P⟧ ⟦Q⟧ = ⟦![1, 1, 0]⟧ := by
  by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
  · rw [addMap_eq, add_of_Y_eq hPz hQz hx hy hy',
      smul_eq _ <| isUnit_dblU_of_Y_eq hP hPz hQz hx hy hy']
  · rw [addMap_eq, add_of_Y_ne hP.left hQ hPz hQz hx hy,
      smul_eq _ <| isUnit_addU_of_Y_ne hPz hQz hy]

/--
@isnad1 id=eq.5h4v.s10.d25ea1821603 from=seed src=0 shape=01306403 vocab=22b102eb
-/
lemma addMap_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) :
    W.addMap ⟦P⟧ ⟦Q⟧ =
      ⟦![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1]⟧ := by
  by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
  · rw [addMap_eq, add_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx,
      smul_eq _ <| isUnit_dblZ_of_Y_ne' hP hQ hPz hx <| not_and.mp hxy hx]
  · rw [addMap_eq, add_of_X_ne hP hQ hPz hQz hx, smul_eq _ <| isUnit_addZ_of_X_ne hx]

/--
@isnad1 id=nonsingu.2h4v.s5.c48f77a6271d from=seed src=0 shape=ed58c234 vocab=208b6ec3
-/
lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
    (hQ : W.NonsingularLift Q) : W.NonsingularLift <| W.addMap P Q := by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

/-! ## Nonsingular Jacobian points -/

variable (W') in
/-- A nonsingular Jacobian point on a Weierstrass curve `W`. -/
@[ext]
structure Point where
  /-- The Jacobian point class underlying a nonsingular Jacobian point on `W`. -/
  {point : PointClass R}
  /-- The nonsingular condition underlying a nonsingular Jacobian point on `W`. -/
  (nonsingular : W'.NonsingularLift point)

namespace Point

/--
@isnad1 id=eq.1h3v.s5.a6dd753a12e8 from=seed src=0 shape=29cf3779 vocab=c1e3890e
-/
lemma mk_point {P : PointClass R} (h : W'.NonsingularLift P) : (mk h).point = P :=
  rfl

instance [Nontrivial R] : Zero W'.Point :=
  ⟨⟨nonsingularLift_zero⟩⟩

/--
@isnad1 id=eq.0h2v.s7.8fa9de9fe435 from=seed src=0 shape=904e9708 vocab=98153a05
-/
lemma zero_def [Nontrivial R] : (0 : W'.Point) = ⟨nonsingularLift_zero⟩ :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.f88af852ed32 from=seed src=0 shape=42d7d623 vocab=0490d45a
-/
lemma zero_point [Nontrivial R] : (0 : W'.Point).point = ⟦![1, 1, 0]⟧ :=
  rfl

/--
@isnad1 id=ne.1h4v.s7.075100606cc3 from=seed src=0 shape=8fa95064 vocab=3d353595
-/
lemma mk_ne_zero [Nontrivial R] {X Y : R} (h : W'.NonsingularLift ⟦![X, Y, 1]⟧) : mk h ≠ 0 :=
  (not_equiv_of_Z_eq_zero_right one_ne_zero rfl).comp <| Quotient.eq.mp.comp Point.ext_iff.mp

/-- The natural map from a nonsingular point on a Weierstrass curve in affine coordinates to its
corresponding nonsingular Jacobian point. -/
def fromAffine [Nontrivial R] : W'.toAffine.Point → W'.Point
  | 0 => 0
  | .some _ _ h => ⟨(nonsingularLift_some ..).mpr h⟩

/--
@isnad1 id=eq.0h2v.s5.5ddac012d958 from=seed src=0 shape=3ba985f6 vocab=2ed2da36
-/
lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W'.Point) :=
  rfl

/--
@isnad1 id=eq.1h4v.s7.e8db0b1c8b12 from=seed src=0 shape=ed5e0f57 vocab=e6d6d29c
-/
lemma fromAffine_some [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some _ _ h) = ⟨(nonsingularLift_some ..).mpr h⟩ :=
  rfl

/--
@isnad1 id=ne.1h4v.s5.663f84020048 from=seed src=0 shape=90054c06 vocab=51464f9a
-/
lemma fromAffine_some_ne_zero [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some _ _ h) ≠ 0 :=
  mk_ne_zero <| (nonsingularLift_some ..).mpr h

/-- The negation of a nonsingular Jacobian point on a Weierstrass curve `W`.

Given a nonsingular Jacobian point `P` on `W`, use `-P` instead of `neg P`. -/
def neg (P : W.Point) : W.Point :=
  ⟨nonsingularLift_negMap P.nonsingular⟩

instance : Neg W.Point :=
  ⟨neg⟩

/--
@isnad1 id=eq.0h3v.s5.d291201cd551 from=seed src=0 shape=633a5599 vocab=00cbae2a
-/
lemma neg_def (P : W.Point) : -P = P.neg :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.a9b28efba44d from=seed src=0 shape=32d7ad1d vocab=e55a1428
-/
lemma neg_point (P : W.Point) : (-P).point = W.negMap P.point :=
  rfl

/-- The addition of two nonsingular Jacobian points on a Weierstrass curve `W`.

Given two nonsingular Jacobian points `P` and `Q` on `W`, use `P + Q` instead of `add P Q`. -/
noncomputable def add (P Q : W.Point) : W.Point :=
  ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩

noncomputable instance : Add W.Point :=
  ⟨add⟩

/--
@isnad1 id=eq.0h4v.s6.98298fb54eea from=seed src=0 shape=b8d343f5 vocab=8eb238a1
-/
lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.c50039a97831 from=seed src=0 shape=6bbf01b0 vocab=9ef04f5d
-/
lemma add_point (P Q : W.Point) : (P + Q).point = W.addMap P.point Q.point :=
  rfl

/-! ## Equivalence between Jacobian and affine coordinates -/

open scoped Classical in
variable (W) in
/-- The natural map from a nonsingular Jacobian point representative on a Weierstrass curve to its
corresponding nonsingular point in affine coordinates. -/
noncomputable def toAffine (P : Fin 3 → F) : W.toAffine.Point :=
  if hP : W.Nonsingular P ∧ P z ≠ 0 then .some _ _ <| (nonsingular_of_Z_ne_zero hP.2).mp hP.1 else 0

/--
@isnad1 id=eq.1h3v.s6.3b556744f210 from=seed src=0 shape=167932fc vocab=a4351b57
-/
lemma toAffine_of_singular {P : Fin 3 → F} (hP : ¬W.Nonsingular P) : toAffine W P = 0 := by
  rw [toAffine, dite_eq_right <| not_and_of_not_left _ hP]

/--
@isnad1 id=eq.1h3v.s6.4b4dab6aaa25 from=seed src=0 shape=a85455b8 vocab=6bc02c0a
-/
lemma toAffine_of_Z_eq_zero {P : Fin 3 → F} (hPz : P z = 0) : toAffine W P = 0 := by
  rw [toAffine, dite_eq_right <| not_and_not_right.mpr fun _ => hPz]

/--
@isnad1 id=eq.0h2v.s6.5843785e0973 from=seed src=0 shape=f1b6f143 vocab=c788c88f
-/
lemma toAffine_zero : toAffine W ![1, 1, 0] = 0 :=
  toAffine_of_Z_eq_zero rfl

/--
@isnad1 id=eq.2h3v.s7.64fd1209f93d from=seed src=0 shape=c224aad3 vocab=ce28d9fa
-/
lemma toAffine_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    toAffine W P = .some _ _ ((nonsingular_of_Z_ne_zero hPz).mp hP) := by
  rw [toAffine, dite_eq_left ⟨hP, hPz⟩]

/--
@isnad1 id=eq.1h4v.s6.84e2375aca3e from=seed src=0 shape=7e1650cc vocab=b3f323dc
-/
lemma toAffine_some {X Y : F} (h : W.Nonsingular ![X, Y, 1]) :
    toAffine W ![X, Y, 1] = .some _ _ ((nonsingular_some ..).mp h) := by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, one_pow, div_one]

/--
@isnad1 id=eq.1h4v.s6.2846feb3cdb6 from=seed src=0 shape=318eafef vocab=94b08e73
-/
lemma toAffine_smul (P : Fin 3 → F) {u : F} (hu : IsUnit u) :
    toAffine W (u • P) = toAffine W P := by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero <| mul_eq_zero_of_right u hPz, toAffine_of_Z_eq_zero hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul P hu).mpr hP) <| mul_ne_zero hu.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_pow, mul_div_mul_left _ _ (hu.pow _).ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (nonsingular_smul P hu).mp, toAffine_of_singular hP]

/--
@isnad1 id=eq.0h5v.s6.331161e013f6 from=seed src=0 shape=e638ee31 vocab=d6e8354d
-/
lemma toAffine_of_equiv {P Q : Fin 3 → F} (h : P ≈ Q) : toAffine W P = toAffine W Q := by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul Q u.isUnit

/--
@isnad1 id=eq.1h3v.s6.790db5f9c263 from=seed src=0 shape=e4787585 vocab=1959e360
-/
lemma toAffine_neg {P : Fin 3 → F} (hP : W.Nonsingular P) :
    toAffine W (W.neg P) = -toAffine W P := by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP hPz,
      toAffine_smul _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg,
      toAffine_zero, toAffine_of_Z_eq_zero hPz, Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul _ <| Ne.isUnit hPz, toAffine_some <|
        (nonsingular_smul _ <| Ne.isUnit hPz).mp <| neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP,
      toAffine_of_Z_ne_zero hP hPz, Affine.Point.neg_some]

private lemma toAffine_add_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) : toAffine W
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] = toAffine W P + toAffine W Q := by
  rw [toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy, toAffine_of_Z_ne_zero hP hPz,
    toAffine_of_Z_ne_zero hQ hQz,
    Affine.Point.add_some <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]]

/--
@isnad1 id=eq.2h4v.s6.1b7d5c56d159 from=seed src=0 shape=87d61ad1 vocab=e53a8684
-/
lemma toAffine_add [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    toAffine W (W.add P Q) = toAffine W P + toAffine W Q := by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hPz, zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2,
        toAffine_zero, toAffine_of_Z_eq_zero hQz]
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz,
        toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ.left hPz hQz,
        toAffine_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg,
        toAffine_of_Z_eq_zero hQz, add_zero]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz, Affine.Point.add_of_Y_eq
            ((X_eq_iff hPz hQz).mp hxy.left) ((Y_eq_iff' hPz hQz).mp hxy.right)]
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · rw [add_of_Y_eq hPz hQz hxy.left hy hxy.right,
            toAffine_smul _ <| isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            toAffine_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, toAffine_zero]
      · have := toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · rwa [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            toAffine_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx <| not_and.mp hxy hx]
        · rwa [add_of_X_ne hP.left hQ.left hPz hQz hx, toAffine_smul _ <| isUnit_addZ_of_X_ne hx]

/-- The natural map from a nonsingular Jacobian point on a Weierstrass curve `W` to its
corresponding nonsingular point in affine coordinates.

If `hP` is the nonsingular condition underlying a nonsingular Jacobian point `P` on `W`, then
`toAffineLift ⟨hP⟩` is definitionally equivalent to `toAffine W P`. -/
noncomputable def toAffineLift (P : W.Point) : W.toAffine.Point :=
  P.point.lift _ fun _ _ => toAffine_of_equiv

/--
@isnad1 id=eq.1h3v.s7.aaa9dc43ef02 from=seed src=0 shape=2e0e6f31 vocab=ca4b092b
-/
lemma toAffineLift_eq {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    toAffineLift ⟨hP⟩ = toAffine W P :=
  rfl

/--
@isnad1 id=eq.2h3v.s7.9b70d5ae0c2a from=seed src=0 shape=51b20300 vocab=87b5f89d
-/
lemma toAffineLift_of_Z_eq_zero {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0) :
    toAffineLift ⟨hP⟩ = 0 :=
  toAffine_of_Z_eq_zero hPz

/--
@isnad1 id=eq.0h2v.s6.da3e483773eb from=seed src=0 shape=81b61fc9 vocab=d13666b9
-/
lemma toAffineLift_zero : toAffineLift (0 : W.Point) = 0 :=
  toAffine_zero

/--
@isnad1 id=eq.2h3v.s8.c5975250abec from=seed src=0 shape=eb6de2e4 vocab=b2f672f0
-/
lemma toAffineLift_of_Z_ne_zero {P : Fin 3 → F} {hP : W.NonsingularLift ⟦P⟧} (hPz : P z ≠ 0) :
    toAffineLift ⟨hP⟩ = .some _ _ ((nonsingular_of_Z_ne_zero hPz).mp hP) :=
  toAffine_of_Z_ne_zero hP hPz

/--
@isnad1 id=eq.1h4v.s8.ea73adac29fb from=seed src=0 shape=0118a577 vocab=3e454f21
-/
lemma toAffineLift_some {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧) :
    toAffineLift ⟨h⟩ = .some _ _ ((nonsingular_some ..).mp h) :=
  toAffine_some h

/--
@isnad1 id=eq.0h3v.s5.4539d7478f7a from=seed src=0 shape=916fff11 vocab=a90ebad9
-/
lemma toAffineLift_neg (P : W.Point) : (-P).toAffineLift = -P.toAffineLift := by
  rcases P with @⟨⟨_⟩, hP⟩
  exact toAffine_neg hP

/--
@isnad1 id=eq.0h4v.s6.7067e2a83cf1 from=seed src=0 shape=8367c54a vocab=d4d57346
-/
lemma toAffineLift_add [DecidableEq F] (P Q : W.Point) :
    (P + Q).toAffineLift = P.toAffineLift + Q.toAffineLift := by
  rcases P, Q with ⟨@⟨⟨_⟩, hP⟩, @⟨⟨_⟩, hQ⟩⟩
  exact toAffine_add hP hQ

set_option backward.isDefEq.respectTransparency false in
variable (W) in
/-- The addition-preserving equivalence between the type of nonsingular Jacobian points on a
Weierstrass curve `W` and the type of nonsingular points in affine coordinates. -/
@[simps]
noncomputable def toAffineAddEquiv [DecidableEq F] : W.Point ≃+ W.toAffine.Point where
  toFun := toAffineLift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, hP⟩
    by_cases hPz : P z = 0
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_eq_zero hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_ne_zero hP hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_some_of_Z_ne_zero hPz
  right_inv := by
    rintro (_ | _)
    · rw [← Affine.Point.zero_def, fromAffine_zero, toAffineLift_zero]
    · rw [fromAffine_some, toAffineLift_some]
  map_add' := toAffineLift_add

noncomputable instance : AddCommGroup W.Point where
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_add _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, zero_add]
  add_zero _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, add_zero]
  neg_add_cancel P := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_neg, neg_add_cancel, toAffineLift_zero]
  add_comm _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_comm]
  add_assoc _ _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_assoc]

end Point

/-! ## Maps and base changes -/

/--
@isnad1 id=eq.0h5v.s7.bffaccb7e3fb from=seed src=0 shape=63cb483b vocab=98c75324
-/
@[simp]
protected lemma map_neg (f : R →+* S) (P : Fin 3 → R) : (W'.map f).neg (f ∘ P) = f ∘ W'.neg P := by
  simp only [neg, map_negY, comp_fin3]
  map_simp

/--
@isnad1 id=eq.2h6v.s8.818ea71952bc from=seed src=0 shape=e788b150 vocab=38f99a53
-/
@[simp]
protected lemma map_add (f : F →+* K) {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : (W.map f).add (f ∘ P) (f ∘ Q) = f ∘ W.add P Q := by
  by_cases h : P ≈ Q
  · rw [add_of_equiv <| (comp_equiv_comp f hP hQ).mpr h, add_of_equiv h, map_dblXYZ]
  · rw [add_of_not_equiv <| h.comp (comp_equiv_comp f hP hQ).mp, add_of_not_equiv h, map_addXYZ]

/--
@isnad1 id=eq.0h7v.s8.a91a371ab2ec from=seed src=0 shape=a29f2889 vocab=1465f31e
-/
lemma baseChange_neg [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B]
    [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B) (P : Fin 3 → A) :
    (W'⁄B).neg (f ∘ P) = f ∘ (W'⁄A).neg P := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Jacobian.map_neg, map_baseChange]

/--
@isnad1 id=eq.2h8v.s8.9ef5a2a1518c from=seed src=0 shape=95ee3db1 vocab=3951e7c1
-/
lemma baseChange_add [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] (f : F →ₐ[S] K) {P Q : Fin 3 → F}
    (hP : (W'⁄F).Nonsingular P) (hQ : (W'⁄F).Nonsingular Q) :
    (W'⁄K).add (f ∘ P) (f ∘ Q) = f ∘ (W'⁄F).add P Q := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Jacobian.map_add _ hP hQ, map_baseChange]

end Jacobian

/-- An abbreviation for `WeierstrassCurve.Jacobian.Point.fromAffine` for dot notation. -/
abbrev Affine.Point.toJacobian [Nontrivial R] {W : Affine R} (P : W.Point) : W.toJacobian.Point :=
  Jacobian.Point.fromAffine P

end WeierstrassCurve
