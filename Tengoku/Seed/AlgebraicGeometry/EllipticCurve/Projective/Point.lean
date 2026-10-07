/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Projective.Formula

/-!
# Nonsingular points and the group law in projective coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular projective points of `W` can be
endowed with a group law, which is uniquely determined by the formulae in
`Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean` and follows from an equivalence
with the nonsingular points in affine coordinates.

This file defines the group law on nonsingular projective points.

## Main definitions

* `WeierstrassCurve.Projective.neg`: the negation of a point representative.
* `WeierstrassCurve.Projective.negMap`: the negation of a point class.
* `WeierstrassCurve.Projective.add`: the addition of two point representatives.
* `WeierstrassCurve.Projective.addMap`: the addition of two point classes.
* `WeierstrassCurve.Projective.Point`: a nonsingular projective point.
* `WeierstrassCurve.Projective.Point.neg`: the negation of a nonsingular projective point.
* `WeierstrassCurve.Projective.Point.add`: the addition of two nonsingular projective points.
* `WeierstrassCurve.Projective.Point.toAffineAddEquiv`: the equivalence between the type of
  nonsingular projective points with the type of nonsingular points in affine coordinates.

## Main statements

* `WeierstrassCurve.Projective.nonsingular_neg`: negation preserves the nonsingular condition.
* `WeierstrassCurve.Projective.nonsingular_add`: addition preserves the nonsingular condition.
* `WeierstrassCurve.Projective.Point.instAddCommGroup`: the type of nonsingular projective points
  forms an abelian group under addition.

## Implementation notes

Note that `W(X, Y, Z)` and its partial derivatives are independent of the point representative, and
the nonsingularity condition already implies `(x, y, z) ≠ (0, 0, 0)`, so a nonsingular projective
point on `W` can be given by `[x : y : z]` and the nonsingular condition on any representative.

A nonsingular projective point representative can be converted to a nonsingular point in affine
coordinates using `WeierstrassCurve.Projective.Point.toAffine`, which lifts to a map on nonsingular
projective points using `WeierstrassCurve.Projective.Point.toAffineLift`. Conversely, a nonsingular
point in affine coordinates can be converted to a nonsingular projective point using
`WeierstrassCurve.Projective.Point.fromAffine` or `WeierstrassCurve.Affine.Point.toProjective`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, projective, point, group law
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

/-! ## Negation on projective point representatives -/

variable (W') in
/-- The negation of a projective point representative on a Weierstrass curve. -/
def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, W'.negY P, P z]

/--
@isnad1 id=eq.0h3v.s5.65bf47bb2246 from=seed src=0 shape=92a61ede vocab=e0ba7c9b
-/
lemma neg_X (P : Fin 3 → R) : W'.neg P x = P x :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.57a3df25a11a from=seed src=0 shape=703fff70 vocab=dabf88f4
-/
lemma neg_Y (P : Fin 3 → R) : W'.neg P y = W'.negY P :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.add558429365 from=seed src=0 shape=92a61ede vocab=e0ba7c9b
-/
lemma neg_Z (P : Fin 3 → R) : W'.neg P z = P z :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.611f5daca582 from=seed src=0 shape=eb1ac6f9 vocab=01a3f2af
-/
protected lemma neg_smul (P : Fin 3 → R) (u : R) : W'.neg (u • P) = u • W'.neg P := by
  simpa only [neg, negY_smul] using! (smul_fin3 (W'.neg P) u).symm

/--
@isnad1 id=equiv.1h4v.s6.c3f34e551044 from=seed src=0 shape=27565bfe vocab=1bfe10c9
-/
lemma neg_smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P :=
  ⟨hu.unit, (W'.neg_smul ..).symm⟩

/--
@isnad1 id=equiv.0h5v.s6.fec81193788d from=seed src=0 shape=0c4360c8 vocab=54081c72
-/
lemma neg_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.neg P ≈ W'.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit

/--
@isnad1 id=eq.2h3v.s7.b99e617cbdad from=seed src=0 shape=9f2df9be vocab=8836a77f
-/
lemma neg_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.neg P = -P y • ![0, 1, 0] := by
  simp [neg, X_eq_zero_of_Z_eq_zero hP hPz, negY_of_Z_eq_zero hP hPz, hPz]

/--
@isnad1 id=eq.1h3v.s8.1884e73518fb from=seed src=0 shape=f4a601dc vocab=54341050
-/
lemma neg_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.neg P = P z • ![P x / P z, W.toAffine.negY (P x / P z) (P y / P z), 1] := by
  erw [neg, smul_fin3, mul_div_cancel₀ _ hPz, ← negY_of_Z_ne_zero hPz, mul_div_cancel₀ _ hPz,
    mul_one]

private lemma nonsingular_neg_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    W.Nonsingular ![P x / P z, W.toAffine.negY (P x / P z) (P y / P z), 1] :=
  (nonsingular_some ..).mpr <| (Affine.nonsingular_neg ..).mpr <|
    (nonsingular_of_Z_ne_zero hPz).mp hP

/--
@isnad1 id=nonsingu.1h3v.s5.478650d22bc4 from=seed src=0 shape=1d875cbd vocab=c301a645
-/
lemma nonsingular_neg {P : Fin 3 → F} (hP : W.Nonsingular P) : W.Nonsingular <| W.neg P := by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP.left hPz, nonsingular_smul _ (isUnit_Y_of_Z_eq_zero hP hPz).neg,
      nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]

/--
@isnad1 id=eq.0h3v.s5.a58bccfd78f5 from=seed src=0 shape=6b37c7ba vocab=54c12ee8
-/
lemma addZ_neg (P : Fin 3 → R) : W'.addZ P (W'.neg P) = 0 := by
  rw [addZ, neg_X, neg_Y, neg_Z, negY]
  ring1

/--
@isnad1 id=eq.0h3v.s5.ddc8a18c510a from=seed src=0 shape=6b37c7ba vocab=1ccaaaa6
-/
lemma addX_neg (P : Fin 3 → R) : W'.addX P (W'.neg P) = 0 := by
  rw [addX, neg_X, neg_Y, neg_Z, negY]
  ring1

/--
@isnad1 id=eq.1h3v.s5.d5e5a7a2c74b from=seed src=0 shape=54e421ef vocab=06c544f5
-/
lemma negAddY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.negAddY P (W'.neg P) = W'.dblZ P := by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -3 * (P y - W'.negY P) * (equation_iff _).mp hP

/--
@isnad1 id=eq.1h3v.s5.d67363e9543a from=seed src=0 shape=d3b6fcf8 vocab=d97bc0c4
-/
lemma addY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W'.dblZ P := by
  simp only [addY, addX_neg, negAddY_neg hP, addZ_neg, negY, fin3_def_ext, mul_zero, sub_zero]

/--
@isnad1 id=eq.1h3v.s7.0a4ddf6be6e9 from=seed src=0 shape=35cb823f vocab=8b217e22
-/
lemma addXYZ_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.addXYZ P (W'.neg P) = -W'.dblZ P • ![0, 1, 0] := by
  erw [addXYZ, addX_neg, addY_neg hP, addZ_neg, smul_fin3, mul_zero, mul_one]

variable (W') in
/-- The negation of a projective point class on a Weierstrass curve `W`.

If `P` is a projective point representative on `W`, then `W.negMap ⟦P⟧` is definitionally equivalent
to `W.neg P`. -/
def negMap (P : PointClass R) : PointClass R :=
  P.map W'.neg fun _ _ => neg_equiv

/--
@isnad1 id=eq.0h3v.s7.e461f548a497 from=seed src=0 shape=a2c7359d vocab=36fe7656
-/
lemma negMap_eq (P : Fin 3 → R) : W'.negMap ⟦P⟧ = ⟦W'.neg P⟧ :=
  rfl

/--
@isnad1 id=eq.2h3v.s8.73ed1d7dfa8a from=seed src=0 shape=4dbbadce vocab=965d1ddb
-/
lemma negMap_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![0, 1, 0]⟧ := by
  rw [negMap_eq, neg_of_Z_eq_zero hP.left hPz, smul_eq _ (isUnit_Y_of_Z_eq_zero hP hPz).neg]

/--
@isnad1 id=eq.1h3v.s8.47671bcb06e2 from=seed src=0 shape=77d3b3ca vocab=12a42664
-/
lemma negMap_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negMap ⟦P⟧ = ⟦![P x / P z, W.toAffine.negY (P x / P z) (P y / P z), 1]⟧ := by
  rw [negMap_eq, neg_of_Z_ne_zero hPz, smul_eq _ <| Ne.isUnit hPz]

/--
@isnad1 id=nonsingu.1h3v.s5.4757e1476391 from=seed src=0 shape=c8b2c16d vocab=11a460c2
-/
lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
    W.NonsingularLift <| W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

/-! ## Addition on projective point representatives -/

open scoped Classical in
variable (W') in
/-- The addition of two projective point representatives on a Weierstrass curve. -/
noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q

/--
@isnad1 id=eq.0h5v.s6.a918d7c73ad1 from=seed src=0 shape=80e8c2f9 vocab=15cb17d5
-/
lemma add_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.add P Q = W'.dblXYZ P :=
  ite_eq_left h

/--
@isnad1 id=eq.2h7v.s8.ca5700040e46 from=seed src=0 shape=b37687a2 vocab=f99ad613
-/
lemma add_smul_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) = u ^ 4 • W'.add P Q := by
  rw [add_of_equiv <| (smul_equiv_smul P Q hu hv).mpr h, dblXYZ_smul, add_of_equiv h]

/--
@isnad1 id=eq.0h3v.s5.e9cc0feff002 from=seed src=0 shape=70894a8f vocab=60faebdf
-/
lemma add_self (P : Fin 3 → R) : W'.add P P = W'.dblXYZ P :=
  add_of_equiv <| Setoid.refl _

/--
@isnad1 id=eq.1h4v.s5.2ea4e0a348d9 from=seed src=0 shape=6c0ae8c0 vocab=60faebdf
-/
lemma add_of_eq {P Q : Fin 3 → R} (h : P = Q) : W'.add P Q = W'.dblXYZ P :=
  h ▸ add_self P

/--
@isnad1 id=eq.1h4v.s6.e47ba2711803 from=seed src=0 shape=995cfb39 vocab=6094a855
-/
lemma add_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q :=
  ite_eq_right h

/--
@isnad1 id=eq.3h6v.s8.56924560055d from=seed src=0 shape=62afc489 vocab=fb8f173d
-/
lemma add_smul_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u)
    (hv : IsUnit v) : W'.add (u • P) (v • Q) = (u * v) ^ 2 • W'.add P Q := by
  rw [add_of_not_equiv <| h.comp (smul_equiv_smul P Q hu hv).mp, addXYZ_smul, add_of_not_equiv h]

/--
@isnad1 id=equiv.2h6v.s7.72bd23018814 from=seed src=0 shape=220ef025 vocab=c403b47d
-/
lemma add_smul_equiv (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) ≈ W'.add P Q := by
  by_cases h : P ≈ Q
  · exact ⟨hu.unit ^ 4, by convert! (add_smul_of_equiv h hu hv).symm⟩
  · exact ⟨(hu.unit * hv.unit) ^ 2, by convert! (add_smul_of_not_equiv h hu hv).symm⟩

/--
@isnad1 id=equiv.0h8v.s6.1b6b775d7d03 from=seed src=0 shape=c15fea32 vocab=2df42560
-/
lemma add_equiv {P P' Q Q' : Fin 3 → R} (hP : P ≈ P') (hQ : Q ≈ Q') :
    W'.add P Q ≈ W'.add P' Q' := by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u.isUnit v.isUnit

/--
@isnad1 id=eq.4h4v.s8.52a4e8d8b18e from=seed src=0 shape=a15432d4 vocab=753d72e2
-/
lemma add_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : W.add P Q = P y ^ 4 • ![0, 1, 0] := by
  rw [add_of_equiv <| equiv_of_Z_eq_zero hP hQ hPz hQz, dblXYZ_of_Z_eq_zero hP.left hPz]

/--
@isnad1 id=eq.3h4v.s8.cd4a63dccad3 from=seed src=0 shape=04343666 vocab=3cb679a0
-/
lemma add_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) (hQz : Q z ≠ 0) : W'.add P Q = (P y ^ 2 * Q z) • Q := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_left hPz hQz, addXYZ_of_Z_eq_zero_left hP hPz]

/--
@isnad1 id=eq.3h4v.s8.4401fb8a5278 from=seed src=0 shape=c688a7cc vocab=641cfb7b
-/
lemma add_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z = 0) : W'.add P Q = -(Q y ^ 2 * P z) • P := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_right hPz hQz, addXYZ_of_Z_eq_zero_right hQ hQz]

/--
@isnad1 id=eq.6h4v.s9.02138ae8e0f9 from=seed src=0 shape=ae9e124a vocab=3489d3fd
-/
lemma add_of_Y_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.add P Q = W.dblU P • ![0, 1, 0] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx hy, dblXYZ_of_Y_eq hP hPz hQz hx hy hy']

/--
@isnad1 id=eq.6h4v.s8.f2f0b58b8f44 from=seed src=0 shape=b236f93c vocab=8dc9f9fc
-/
lemma add_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ Q y * P z) :
    W.add P Q = addU P Q • ![0, 1, 0] := by
  rw [add_of_not_equiv <| not_equiv_of_Y_ne hy, addXYZ_of_X_eq hP hQ hPz hQz hx]

/--
@isnad1 id=eq.6h4v.s10.16ed66ec04bc from=seed src=0 shape=5714f51b vocab=d1ef8b98
-/
lemma add_of_Y_ne' [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.add P Q = W.dblZ P •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx <| Y_eq_of_Y_ne' hP hQ hPz hQz hx hy,
    dblXYZ_of_Z_ne_zero hP hQ hPz hQz hx hy]

/--
@isnad1 id=eq.5h4v.s10.8c25dd00886d from=seed src=0 shape=4696396e vocab=0ab93f07
-/
lemma add_of_X_ne [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.add P Q = W.addZ P Q •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
  rw [add_of_not_equiv <| not_equiv_of_X_ne hx, addXYZ_of_Z_ne_zero hP hQ hPz hQz hx]

private lemma nonsingular_add_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z)) : W.Nonsingular
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] :=
  (nonsingular_some ..).mpr <| Affine.nonsingular_add ((nonsingular_of_Z_ne_zero hPz).mp hP)
    ((nonsingular_of_Z_ne_zero hQz).mp hQ) <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]

/--
@isnad1 id=nonsingu.2h4v.s5.a4bc03c92782 from=seed src=0 shape=a8334ee2 vocab=03690f00
-/
lemma nonsingular_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Nonsingular <| W.add P Q := by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz,
        nonsingular_smul _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
        nonsingular_smul _ <| ((isUnit_Y_of_Z_eq_zero hP hPz).pow 2).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ (((isUnit_Y_of_Z_eq_zero hQ hQz).pow 2).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z
      · by_cases hy : P y * Q z = Q y * P z
        · simp only [add_of_Y_eq hP.left hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            nonsingular_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · classical
        have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z = Q x * P z
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            nonsingular_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hQz hx <|
              not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
            nonsingular_smul _ <| isUnit_addZ_of_X_ne hP.left hQ.left hx]

variable (W') in
/-- The addition of two projective point classes on a Weierstrass curve `W`.

If `P` and `Q` are two projective point representatives on `W`, then `W.addMap ⟦P⟧ ⟦Q⟧` is
definitionally equivalent to `W.add P Q`. -/
noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

/--
@isnad1 id=eq.0h4v.s8.adcf7f9ba4ce from=seed src=0 shape=c13e2c50 vocab=dded7a50
-/
lemma addMap_eq (P Q : Fin 3 → R) : W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧ :=
  rfl

/--
@isnad1 id=eq.3h4v.s7.33c2949366a6 from=seed src=0 shape=9e4a260b vocab=b5c2fe2d
-/
lemma addMap_of_Z_eq_zero_left {P : Fin 3 → F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  revert hQ
  refine Q.inductionOn (motive := fun Q => _ → W.addMap _ Q = Q) fun Q hQ => ?_
  by_cases hQz : Q z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hQ hQz
  · rw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
      smul_eq _ <| ((isUnit_Y_of_Z_eq_zero hP hPz).pow 2).mul <| Ne.isUnit hQz]

/--
@isnad1 id=eq.3h4v.s7.77983199d123 from=seed src=0 shape=a15afd33 vocab=b5c2fe2d
-/
lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 → F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  revert hP
  refine P.inductionOn (motive := fun P => _ → W.addMap P _ = P) fun P hP => ?_
  by_cases hPz : P z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
  · rw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ (((isUnit_Y_of_Z_eq_zero hQ hQz).pow 2).mul <| Ne.isUnit hPz).neg]

/--
@isnad1 id=eq.6h4v.s9.0fac0dccc943 from=seed src=0 shape=a50462e1 vocab=bc38b7b0
-/
lemma addMap_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.addMap ⟦P⟧ ⟦Q⟧ = ⟦![0, 1, 0]⟧ := by
  by_cases hy : P y * Q z = Q y * P z
  · rw [addMap_eq, add_of_Y_eq hP.left hPz hQz hx hy hy',
      smul_eq _ <| isUnit_dblU_of_Y_eq hP hPz hQz hx hy hy']
  · rw [addMap_eq, add_of_Y_ne hP.left hQ hPz hQz hx hy,
      smul_eq _ <| isUnit_addU_of_Y_ne hPz hQz hy]

/--
@isnad1 id=eq.5h4v.s10.552194947eb8 from=seed src=0 shape=3f295ea1 vocab=a36047fb
-/
lemma addMap_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hxy : ¬(P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z)) :
    W.addMap ⟦P⟧ ⟦Q⟧ =
      ⟦![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1]⟧ := by
  by_cases hx : P x * Q z = Q x * P z
  · rw [addMap_eq, add_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx,
      smul_eq _ <| isUnit_dblZ_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx]
  · rw [addMap_eq, add_of_X_ne hP hQ hPz hQz hx, smul_eq _ <| isUnit_addZ_of_X_ne hP hQ hx]

/--
@isnad1 id=nonsingu.2h4v.s5.d0f615bfe09b from=seed src=0 shape=ed58c234 vocab=92bbaea3
-/
lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
    (hQ : W.NonsingularLift Q) : W.NonsingularLift <| W.addMap P Q := by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

/-! ## Nonsingular projective points -/

variable (W') in
/-- A nonsingular projective point on a Weierstrass curve `W`. -/
@[ext]
structure Point where
  /-- The projective point class underlying a nonsingular projective point on `W`. -/
  {point : PointClass R}
  /-- The nonsingular condition underlying a nonsingular projective point on `W`. -/
  (nonsingular : W'.NonsingularLift point)

namespace Point

/--
@isnad1 id=eq.1h3v.s5.189c5424427a from=seed src=0 shape=29cf3779 vocab=c6574e6d
-/
lemma mk_point {P : PointClass R} (h : W'.NonsingularLift P) : (mk h).point = P :=
  rfl

instance [Nontrivial R] : Zero W'.Point :=
  ⟨⟨nonsingularLift_zero⟩⟩

/--
@isnad1 id=eq.0h2v.s7.48de44401d07 from=seed src=0 shape=904e9708 vocab=e0143f49
-/
lemma zero_def [Nontrivial R] : (0 : W'.Point) = ⟨nonsingularLift_zero⟩ :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.9dcba34a2be3 from=seed src=0 shape=42d7d623 vocab=4bc3272f
-/
lemma zero_point [Nontrivial R] : (0 : W'.Point).point = ⟦![0, 1, 0]⟧ :=
  rfl

/--
@isnad1 id=ne.1h4v.s8.3378fd5cf238 from=seed src=0 shape=8fa95064 vocab=2b126ad7
-/
lemma mk_ne_zero [Nontrivial R] {X Y : R} (h : W'.NonsingularLift ⟦![X, Y, 1]⟧) : mk h ≠ 0 :=
  (not_equiv_of_Z_eq_zero_right one_ne_zero rfl).comp <| Quotient.eq.mp.comp Point.ext_iff.mp

/-- The natural map from a nonsingular point on a Weierstrass curve in affine coordinates to its
corresponding nonsingular projective point. -/
def fromAffine [Nontrivial R] : W'.toAffine.Point → W'.Point
  | 0 => 0
  | .some _ _ h => ⟨(nonsingularLift_some ..).mpr h⟩

/--
@isnad1 id=eq.0h2v.s5.d61d4fdf4d16 from=seed src=0 shape=3ba985f6 vocab=eacffdbf
-/
lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W'.Point) :=
  rfl

/--
@isnad1 id=eq.1h4v.s7.ad2d0d3a9e38 from=seed src=0 shape=ed5e0f57 vocab=50a1eec4
-/
lemma fromAffine_some [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some _ _ h) = ⟨(nonsingularLift_some ..).mpr h⟩ :=
  rfl

/--
@isnad1 id=ne.1h4v.s5.f99bdc3c5e67 from=seed src=0 shape=90054c06 vocab=8a4c2e19
-/
lemma fromAffine_some_ne_zero [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some _ _ h) ≠ 0 :=
  mk_ne_zero <| (nonsingularLift_some ..).mpr h

/-- The negation of a nonsingular projective point on a Weierstrass curve `W`.

Given a nonsingular projective point `P` on `W`, use `-P` instead of `neg P`. -/
def neg (P : W.Point) : W.Point :=
  ⟨nonsingularLift_negMap P.nonsingular⟩

instance : Neg W.Point :=
  ⟨neg⟩

/--
@isnad1 id=eq.0h3v.s5.5ef7bc9666c7 from=seed src=0 shape=633a5599 vocab=30394bcb
-/
lemma neg_def (P : W.Point) : -P = P.neg :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.28d7b4f299c7 from=seed src=0 shape=32d7ad1d vocab=6f372c97
-/
lemma neg_point (P : W.Point) : (-P).point = W.negMap P.point :=
  rfl

/-- The addition of two nonsingular projective points on a Weierstrass curve `W`.

Given two nonsingular projective points `P` and `Q` on `W`, use `P + Q` instead of `add P Q`. -/
noncomputable def add (P Q : W.Point) : W.Point :=
  ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩

noncomputable instance : Add W.Point :=
  ⟨add⟩

/--
@isnad1 id=eq.0h4v.s6.fde190ccbc33 from=seed src=0 shape=b8d343f5 vocab=fc43ff41
-/
lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.8eeacf44e2d2 from=seed src=0 shape=6bbf01b0 vocab=052d318f
-/
lemma add_point (P Q : W.Point) : (P + Q).point = W.addMap P.point Q.point :=
  rfl

/-! ## Equivalence between projective and affine coordinates -/

open scoped Classical in
variable (W) in
/-- The natural map from a nonsingular projective point representative on a Weierstrass curve to its
corresponding nonsingular point in affine coordinates. -/
noncomputable def toAffine (P : Fin 3 → F) : W.toAffine.Point :=
  if hP : W.Nonsingular P ∧ P z ≠ 0 then .some _ _ <| (nonsingular_of_Z_ne_zero hP.2).mp hP.1 else 0

/--
@isnad1 id=eq.1h3v.s6.afccdb613e08 from=seed src=0 shape=167932fc vocab=14478b8b
-/
lemma toAffine_of_singular {P : Fin 3 → F} (hP : ¬W.Nonsingular P) : toAffine W P = 0 := by
  rw [toAffine, dite_eq_right <| not_and_of_not_left _ hP]

/--
@isnad1 id=eq.1h3v.s6.f9e14e376e38 from=seed src=0 shape=a85455b8 vocab=ef74441e
-/
lemma toAffine_of_Z_eq_zero {P : Fin 3 → F} (hPz : P z = 0) : toAffine W P = 0 := by
  rw [toAffine, dite_eq_right <| not_and_not_right.mpr fun _ => hPz]

/--
@isnad1 id=eq.0h2v.s6.de97dccc9291 from=seed src=0 shape=f1b6f143 vocab=afa2aec8
-/
lemma toAffine_zero : toAffine W ![0, 1, 0] = 0 :=
  toAffine_of_Z_eq_zero rfl

/--
@isnad1 id=eq.2h3v.s7.7285825f7c96 from=seed src=0 shape=ce889d10 vocab=763f5814
-/
lemma toAffine_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    toAffine W P = .some _ _ ((nonsingular_of_Z_ne_zero hPz).mp hP) := by
  rw [toAffine, dite_eq_left ⟨hP, hPz⟩]

/--
@isnad1 id=eq.1h4v.s6.32d9ee582774 from=seed src=0 shape=7e1650cc vocab=c8578a00
-/
lemma toAffine_some {X Y : F} (h : W.Nonsingular ![X, Y, 1]) :
    toAffine W ![X, Y, 1] = .some _ _ ((nonsingular_some ..).mp h) := by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, div_one]

/--
@isnad1 id=eq.1h4v.s6.ad81edbabf15 from=seed src=0 shape=318eafef vocab=4ef326e2
-/
lemma toAffine_smul (P : Fin 3 → F) {u : F} (hu : IsUnit u) :
    toAffine W (u • P) = toAffine W P := by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero <| mul_eq_zero_of_right u hPz, toAffine_of_Z_eq_zero hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul P hu).mpr hP) <| mul_ne_zero hu.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_div_mul_left _ _ hu.ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (nonsingular_smul P hu).mp, toAffine_of_singular hP]

/--
@isnad1 id=eq.0h5v.s6.d5b65a0ac593 from=seed src=0 shape=e638ee31 vocab=7378a4dc
-/
lemma toAffine_of_equiv {P Q : Fin 3 → F} (h : P ≈ Q) : toAffine W P = toAffine W Q := by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul Q u.isUnit

/--
@isnad1 id=eq.1h3v.s6.4557e47f702c from=seed src=0 shape=e4787585 vocab=6a692b66
-/
lemma toAffine_neg {P : Fin 3 → F} (hP : W.Nonsingular P) :
    toAffine W (W.neg P) = -toAffine W P := by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP.left hPz, toAffine_smul _ (isUnit_Y_of_Z_eq_zero hP hPz).neg,
      toAffine_zero, toAffine_of_Z_eq_zero hPz, Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul _ <| Ne.isUnit hPz, toAffine_some <|
        (nonsingular_smul _ <| Ne.isUnit hPz).mp <| neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP,
      toAffine_of_Z_ne_zero hP hPz, Affine.Point.neg_some]

private lemma toAffine_add_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z)) : toAffine W
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        1] = toAffine W P + toAffine W Q := by
  rw [toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy, toAffine_of_Z_ne_zero hP hPz,
    toAffine_of_Z_ne_zero hQ hQz,
    Affine.Point.add_some <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]]

/--
@isnad1 id=eq.2h4v.s6.67e293dbe1bb from=seed src=0 shape=87d61ad1 vocab=6abd0cf3
-/
lemma toAffine_add [DecidableEq F] {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    toAffine W (W.add P Q) = toAffine W P + toAffine W Q := by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hPz, zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4,
        toAffine_zero, toAffine_of_Z_eq_zero hQz]
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz,
        toAffine_smul _ <| ((isUnit_Y_of_Z_eq_zero hP hPz).pow 2).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ.left hPz hQz,
        toAffine_smul _ (((isUnit_Y_of_Z_eq_zero hQ hQz).pow 2).mul <| Ne.isUnit hPz).neg,
        toAffine_of_Z_eq_zero hQz, add_zero]
    · by_cases hxy : P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z
      · rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz, Affine.Point.add_of_Y_eq
            ((X_eq_iff hPz hQz).mp hxy.left) ((Y_eq_iff' hPz hQz).mp hxy.right)]
        by_cases hy : P y * Q z = Q y * P z
        · rw [add_of_Y_eq hP.left hPz hQz hxy.left hy hxy.right,
            toAffine_smul _ <| isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            toAffine_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, toAffine_zero]
      · have := toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z = Q x * P z
        · rwa [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            toAffine_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx]
        · rwa [add_of_X_ne hP.left hQ.left hPz hQz hx,
            toAffine_smul _ <| isUnit_addZ_of_X_ne hP.left hQ.left hx]

/-- The natural map from a nonsingular projective point on a Weierstrass curve `W` to its
corresponding nonsingular point in affine coordinates.

If `hP` is the nonsingular condition underlying a nonsingular projective point `P` on `W`, then
`toAffineLift ⟨hP⟩` is definitionally equivalent to `toAffine W P`. -/
noncomputable def toAffineLift (P : W.Point) : W.toAffine.Point :=
  P.point.lift _ fun _ _ => toAffine_of_equiv

/--
@isnad1 id=eq.1h3v.s7.277fc7a0cbf9 from=seed src=0 shape=2e0e6f31 vocab=7e487614
-/
lemma toAffineLift_eq {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    toAffineLift ⟨hP⟩ = toAffine W P :=
  rfl

/--
@isnad1 id=eq.2h3v.s8.21ee904f76c1 from=seed src=0 shape=51b20300 vocab=55f4dfca
-/
lemma toAffineLift_of_Z_eq_zero {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0) :
    toAffineLift ⟨hP⟩ = 0 :=
  toAffine_of_Z_eq_zero hPz

/--
@isnad1 id=eq.0h2v.s6.601492918d7b from=seed src=0 shape=81b61fc9 vocab=0daa277c
-/
lemma toAffineLift_zero : toAffineLift (0 : W.Point) = 0 :=
  toAffine_zero

/--
@isnad1 id=eq.2h3v.s8.fad73f324d7c from=seed src=0 shape=15595fab vocab=c4b62f63
-/
lemma toAffineLift_of_Z_ne_zero {P : Fin 3 → F} {hP : W.NonsingularLift ⟦P⟧} (hPz : P z ≠ 0) :
    toAffineLift ⟨hP⟩ = .some _ _ ((nonsingular_of_Z_ne_zero hPz).mp hP) :=
  toAffine_of_Z_ne_zero hP hPz

/--
@isnad1 id=eq.1h4v.s8.34c08e228e88 from=seed src=0 shape=0118a577 vocab=4a114126
-/
lemma toAffineLift_some {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧) :
    toAffineLift ⟨h⟩ = .some _ _ ((nonsingular_some ..).mp h) :=
  toAffine_some h

/--
@isnad1 id=eq.0h3v.s5.758d733d5f13 from=seed src=0 shape=916fff11 vocab=abaf84a1
-/
lemma toAffineLift_neg (P : W.Point) : (-P).toAffineLift = -P.toAffineLift := by
  rcases P with @⟨⟨_⟩, hP⟩
  exact toAffine_neg hP

/--
@isnad1 id=eq.0h4v.s6.9cec17bb5c18 from=seed src=0 shape=8367c54a vocab=079d7bd3
-/
lemma toAffineLift_add [DecidableEq F] (P Q : W.Point) :
    (P + Q).toAffineLift = P.toAffineLift + Q.toAffineLift := by
  rcases P, Q with ⟨@⟨⟨_⟩, hP⟩, @⟨⟨_⟩, hQ⟩⟩
  exact toAffine_add hP hQ

set_option backward.isDefEq.respectTransparency false in
variable (W) in
/-- The addition-preserving equivalence between the type of nonsingular projective points on a
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
@isnad1 id=eq.0h5v.s7.043d9550328c from=seed src=0 shape=63cb483b vocab=79a0438a
-/
@[simp]
protected lemma map_neg (f : R →+* S) (P : Fin 3 → R) : (W'.map f).neg (f ∘ P) = f ∘ W'.neg P := by
  simp only [neg, map_negY, comp_fin3]
  map_simp

/--
@isnad1 id=eq.2h6v.s8.4499d79381a0 from=seed src=0 shape=e788b150 vocab=8e794d98
-/
@[simp]
protected lemma map_add (f : F →+* K) {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : (W.map f).add (f ∘ P) (f ∘ Q) = f ∘ W.add P Q := by
  by_cases h : P ≈ Q
  · rw [add_of_equiv <| (comp_equiv_comp f hP hQ).mpr h, add_of_equiv h, map_dblXYZ]
  · rw [add_of_not_equiv <| h.comp (comp_equiv_comp f hP hQ).mp, add_of_not_equiv h, map_addXYZ]

/--
@isnad1 id=eq.0h7v.s8.98b84dd54b4f from=seed src=0 shape=a29f2889 vocab=cf2276dd
-/
lemma baseChange_neg [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B]
    [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B) (P : Fin 3 → A) :
    (W'⁄B).neg (f ∘ P) = f ∘ (W'⁄A).neg P := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Projective.map_neg, map_baseChange]

/--
@isnad1 id=eq.2h8v.s8.440b8fcec764 from=seed src=0 shape=95ee3db1 vocab=fb7328cf
-/
lemma baseChange_add [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] (f : F →ₐ[S] K) {P Q : Fin 3 → F}
    (hP : (W'⁄F).Nonsingular P) (hQ : (W'⁄F).Nonsingular Q) :
    (W'⁄K).add (f ∘ P) (f ∘ Q) = f ∘ (W'⁄F).add P Q := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Projective.map_add _ hP hQ, map_baseChange]

end Projective

/-- An abbreviation for `WeierstrassCurve.Projective.Point.fromAffine` for dot notation. -/
abbrev Affine.Point.toProjective [Nontrivial R] {W : Affine R} (P : W.Point) :
    W.toProjective.Point :=
  Projective.Point.fromAffine P

end WeierstrassCurve
