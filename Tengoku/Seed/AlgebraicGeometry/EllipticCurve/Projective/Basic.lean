/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.MvPolynomial.PDeriv
public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Tengoku.Seed.Data.Fin.Tuple.Reflection
public import Tengoku.Seed.Tactic.Ring.NamePolyVars

/-!
# Weierstrass equations and the nonsingular condition in projective coordinates

A point on the unweighted projective plane over a commutative ring `R` is an equivalence class
`[x : y : z]` of triples `(x, y, z) ≠ (0, 0, 0)` of elements in `R` such that
`(x, y, z) ∼ (x', y', z')` if there is some unit `u` in `Rˣ` with `(x, y, z) = (ux', uy', uz')`.

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. A
*projective point* is a point on the unweighted projective plane over `R` satisfying the
*homogeneous Weierstrass equation* `W(X, Y, Z) = 0` in *projective coordinates*, where
`W(X, Y, Z) := Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`. It is *nonsingular* if its
partial derivatives `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_Z(x, y, z)` do not vanish simultaneously.

This file gives an explicit implementation of equivalence classes of triples up to scaling by units,
and defines polynomials associated to Weierstrass equations and the nonsingular condition in
projective coordinates. The group law on the actual type of nonsingular projective points will be
defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`, based on the formulae
for group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`.

## Main definitions

* `WeierstrassCurve.Projective.PointClass`: the equivalence class of a point representative.
* `WeierstrassCurve.Projective.Nonsingular`: the nonsingular condition on a point representative.
* `WeierstrassCurve.Projective.NonsingularLift`: the nonsingular condition on a point class.

## Main statements

* `WeierstrassCurve.Projective.polynomial_relation`: Euler's homogeneous function theorem.

## Implementation notes

All definitions and lemmas for Weierstrass curves in projective coordinates live in the namespace
`WeierstrassCurve.Projective` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toProjective`.
This can be converted into `WeierstrassCurve.Affine` using `WeierstrassCurve.Projective.toAffine`.

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not definitionally equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not definitionally equal to `![u * Q x, u * Q y, u * Q z]`, so the
lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms. Files in
`Mathlib/AlgebraicGeometry/EllipticCurve/Projective` make extensive use of `erw` to get around this.
While `erw` is often an indication of a problem, in this case it is self-contained and should not
cause any issues. It would alternatively be possible to add some automation to assist here.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, projective, Weierstrass equation, nonsingular
-/

@[expose] public section

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

local macro "pderiv_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,
    pderiv_X_of_ne (by decide : z ≠ x), pderiv_X_of_ne (by decide : x ≠ z),
    pderiv_X_of_ne (by decide : z ≠ y), pderiv_X_of_ne (by decide : y ≠ z)])

universe r s u v

variable {R : Type r} {F : Type u}

name_poly_vars X, Y, Z over R

namespace WeierstrassCurve

/-! ## Projective coordinates -/

variable (R) in
/-- An abbreviation for a Weierstrass curve in projective coordinates. -/
abbrev Projective : Type r :=
  WeierstrassCurve R

/-- The conversion from a Weierstrass curve to projective coordinates. -/
abbrev toProjective (W : WeierstrassCurve R) : Projective R :=
  W

namespace Projective

/-- The conversion from a Weierstrass curve in projective coordinates to affine coordinates. -/
abbrev toAffine (W' : Projective R) : Affine R :=
  W'

/--
@isnad1 id=eq.0h2v.s6.3ccc0fff01a4 from=seed src=0 shape=b13a1fd3 vocab=4e3792ea
-/
lemma fin3_def (P : Fin 3 → R) : ![P x, P y, P z] = P := by
  ext n; fin_cases n <;> rfl

/--
@isnad1 id=and.0h4v.s7.397088f3fea9 from=seed src=0 shape=516fa6da vocab=4e3792ea
-/
lemma fin3_def_ext (a b c : R) : ![a, b, c] x = a ∧ ![a, b, c] y = b ∧ ![a, b, c] z = c :=
  ⟨rfl, rfl, rfl⟩

/--
@isnad1 id=eq.0h6v.s6.5371acfb47a7 from=seed src=0 shape=8c8515c6 vocab=3dd43b50
-/
lemma comp_fin3 {S : Type s} (f : R → S) (a b c : R) : f ∘ ![a, b, c] = ![f a, f b, f c] :=
  (FinVec.map_eq ..).symm

variable [CommRing R] [Field F] {W' : Projective R} {W : Projective F} {S : Type s} [CommRing S]
  {A : Type u} [CommRing A] {B : Type v} [CommRing B] {K : Type v} [Field K]

/--
@isnad1 id=eq.0h3v.s7.246b99ebd1ec from=seed src=0 shape=8e1ebc04 vocab=1daae00e
-/
lemma smul_fin3 (P : Fin 3 → R) (u : R) : u • P = ![u * P x, u * P y, u * P z] := by
  simp [← List.ofFn_inj, List.ofFn_succ]

/--
@isnad1 id=and.0h3v.s8.276611ad1747 from=seed src=0 shape=78305e63 vocab=5e9cb1f7
-/
lemma smul_fin3_ext (P : Fin 3 → R) (u : R) :
    (u • P) x = u * P x ∧ (u • P) y = u * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩

/--
@isnad1 id=eq.0h5v.s8.3caa5a08f929 from=seed src=0 shape=eb8e3ac3 vocab=17aa807b
-/
lemma comp_smul (f : R →+* S) (P : Fin 3 → R) (u : R) : f ∘ (u • P) = f u • f ∘ P := by
  ext
  simp

/-- The equivalence setoid for a projective point representative on a Weierstrass curve. -/
@[reducible]
scoped instance : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

variable (R) in
/-- The equivalence class of a projective point representative on a Weierstrass curve. -/
abbrev PointClass : Type r :=
  MulAction.orbitRel.Quotient Rˣ <| Fin 3 → R

/--
@isnad1 id=equiv.1h3v.s6.1ddd771dc9ef from=seed src=0 shape=3d19466f vocab=7a2da90c
-/
lemma smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : u • P ≈ P :=
  ⟨hu.unit, rfl⟩

/--
@isnad1 id=eq.1h3v.s8.af644b5d63f0 from=seed src=0 shape=85116117 vocab=80862c38
-/
@[simp]
lemma smul_eq (P : Fin 3 → R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
  Quotient.eq.mpr <| smul_equiv P hu

/--
@isnad1 id=iff.2h5v.s7.d883d2240691 from=seed src=0 shape=d6f15e0f vocab=7a2da90c
-/
lemma smul_equiv_smul (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    u • P ≈ v • Q ↔ P ≈ Q := by
  rw [← Quotient.eq_iff_equiv, ← Quotient.eq_iff_equiv, smul_eq P hu, smul_eq Q hv]

/--
@isnad1 id=iff.2h3v.s7.a306d1bb01b9 from=seed src=0 shape=8ffaa130 vocab=21cd50ab
-/
lemma equiv_iff_eq_of_Z_eq' {P Q : Fin 3 → R} (hz : P z = Q z) (hQz : Q z ∈ nonZeroDivisors R) :
    P ≈ Q ↔ P = Q := by
  refine ⟨?_, Quotient.exact.comp <| congrArg _⟩
  rintro ⟨u, rfl⟩
  simp only [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors hQz).mp <| one_mul (Q z) ▸ hz]
  rw [one_smul]

/--
@isnad1 id=iff.2h3v.s7.236f206401be from=seed src=0 shape=7940b1a1 vocab=bf024407
-/
lemma equiv_iff_eq_of_Z_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hz : P z = Q z) (hQz : Q z ≠ 0) :
    P ≈ Q ↔ P = Q :=
  equiv_iff_eq_of_Z_eq' hz <| mem_nonZeroDivisors_of_ne_zero hQz

/--
@isnad1 id=iff.0h4v.s6.748f4a6eba77 from=seed src=0 shape=3fbb5afd vocab=9c624857
-/
lemma Z_eq_zero_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨_, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext, Units.mul_right_eq_zero]

/--
@isnad1 id=eq.0h4v.s7.604765e9c5bf from=seed src=0 shape=d0a8f441 vocab=312537d8
-/
lemma X_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P x * Q z = Q x * P z := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.0h4v.s7.c02e1cf195ff from=seed src=0 shape=d0a8f441 vocab=312537d8
-/
lemma Y_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P y * Q z = Q y * P z := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

/--
@isnad1 id=not.2h3v.s6.0e0a73c2238a from=seed src=0 shape=cdf86fe4 vocab=9c624857
-/
lemma not_equiv_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) (hQz : Q z ≠ 0) : ¬P ≈ Q :=
  fun h => hQz <| (Z_eq_zero_of_equiv h).mp hPz

/--
@isnad1 id=not.2h3v.s6.b3c844a1453b from=seed src=0 shape=cdf86fe4 vocab=9c624857
-/
lemma not_equiv_of_Z_eq_zero_right {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z = 0) : ¬P ≈ Q :=
  fun h => hPz <| (Z_eq_zero_of_equiv h).mpr hQz

/--
@isnad1 id=not.1h3v.s7.2990acff0f17 from=seed src=0 shape=b65020d0 vocab=312537d8
-/
lemma not_equiv_of_X_ne {P Q : Fin 3 → R} (hx : P x * Q z ≠ Q x * P z) : ¬P ≈ Q :=
  hx.comp X_eq_of_equiv

/--
@isnad1 id=not.1h3v.s7.0d3d7dfdaaf0 from=seed src=0 shape=b65020d0 vocab=312537d8
-/
lemma not_equiv_of_Y_ne {P Q : Fin 3 → R} (hy : P y * Q z ≠ Q y * P z) : ¬P ≈ Q :=
  hy.comp Y_eq_of_equiv

/--
@isnad1 id=equiv.4h3v.s8.cfb1563faf17 from=seed src=0 shape=f7847543 vocab=46efdf99
-/
lemma equiv_of_X_eq_of_Y_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) : P ≈ Q := by
  use Units.mk0 _ hPz / Units.mk0 _ hQz
  simp only [Units.smul_def, smul_fin3, Units.val_div_eq_div_val, Units.val_mk0, mul_comm, mul_div,
    ← hx, ← hy, mul_div_cancel_right₀ _ hQz, fin3_def]

/--
@isnad1 id=equiv.1h2v.s7.1848f59a4a28 from=seed src=0 shape=345e039f vocab=10be90f1
-/
lemma equiv_some_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : P ≈ ![P x / P z, P y / P z, 1] :=
  equiv_of_X_eq_of_Y_eq hPz one_ne_zero
    (by linear_combination (norm := (matrix_simp; ring1)) -P x * div_self hPz)
    (by linear_combination (norm := (matrix_simp; ring1)) -P y * div_self hPz)

/--
@isnad1 id=iff.2h3v.s8.c0e613e6b8dd from=seed src=0 shape=22738df1 vocab=acb031af
-/
lemma X_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P x * Q z = Q x * P z ↔ P x / P z = Q x / Q z :=
  (div_eq_div_iff hPz hQz).symm

/--
@isnad1 id=iff.2h3v.s8.61a88c2b3e58 from=seed src=0 shape=22738df1 vocab=acb031af
-/
lemma Y_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z = Q y * P z ↔ P y / P z = Q y / Q z :=
  (div_eq_div_iff hPz hQz).symm

/-! ## Weierstrass equations in projective coordinates -/

variable (W') in
/-- The polynomial `W(X, Y, Z) := Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)` associated to a
Weierstrass curve `W` over a ring `R` in projective coordinates.

This is represented as a term of type `MvPolynomial (Fin 3) R`, where `X`, `Y`, and `Z`
represent `X`, `Y`, and `Z` respectively. -/
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  Y ^ 2 * Z + C W'.a₁ * X * Y * Z + C W'.a₃ * Y * Z ^ 2
    - (X ^ 3 + C W'.a₂ * X ^ 2 * Z + C W'.a₄ * X * Z ^ 2 + C W'.a₆ * Z ^ 3)

/--
@isnad1 id=eq.0h3v.s9.8df58d3d85ba from=seed src=0 shape=437439d6 vocab=58fc8702
-/
lemma eval_polynomial (P : Fin 3 → R) : eval P W'.polynomial =
    P y ^ 2 * P z + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 2
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z + W'.a₄ * P x * P z ^ 2 + W'.a₆ * P z ^ 3) := by
  rw [polynomial]
  simp

/--
@isnad1 id=eq.1h3v.s8.a13bc449957f from=seed src=0 shape=3b9ae472 vocab=00436bf8
-/
lemma eval_polynomial_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : eval P W.polynomial / P z ^ 3 =
    W.toAffine.polynomial.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomial, Affine.evalEval_polynomial]; ring1))
    P y ^ 2 / P z ^ 2 * div_self hPz + W.a₁ * P x * P y / P z ^ 2 * div_self hPz
      + W.a₃ * P y / P z * div_self (pow_ne_zero 2 hPz) - W.a₂ * P x ^ 2 / P z ^ 2 * div_self hPz
      - W.a₄ * P x / P z * div_self (pow_ne_zero 2 hPz) - W.a₆ * div_self (pow_ne_zero 3 hPz)

variable (W') in
/-- The proposition that a projective point representative `(x, y, z)` lies in a Weierstrass curve
`W`.

In other words, it satisfies the homogeneous Weierstrass equation `W(X, Y, Z) = 0`. -/
def Equation (P : Fin 3 → R) : Prop :=
  eval P W'.polynomial = 0

/--
@isnad1 id=iff.0h3v.s9.1c8d10e6c92a from=seed src=0 shape=b244d2b2 vocab=e260c735
-/
lemma equation_iff (P : Fin 3 → R) : W'.Equation P ↔
    P y ^ 2 * P z + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 2
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z + W'.a₄ * P x * P z ^ 2 + W'.a₆ * P z ^ 3) = 0 := by
  rw [Equation, eval_polynomial, sub_eq_zero]

/--
@isnad1 id=iff.1h4v.s6.387dc455eb61 from=seed src=0 shape=53a15692 vocab=7890364d
-/
lemma equation_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P :=
  have hP (u : R) {P : Fin 3 → R} (hP : W'.Equation P) : W'.Equation <| u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 3 * hP
  ⟨fun h => by convert! hP (↑hu.unit⁻¹) h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩

/--
@isnad1 id=iff.0h5v.s5.4de0e18116c5 from=seed src=0 shape=d37c1894 vocab=4fe74a65
-/
lemma equation_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

/--
@isnad1 id=iff.1h3v.s6.e308b452d249 from=seed src=0 shape=b074693f vocab=5d91549a
-/
lemma equation_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.Equation P ↔ P x ^ 3 = 0 := by
  simp only [equation_iff, hPz, add_zero, zero_sub, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _,
    neg_eq_zero]

/--
@isnad1 id=equation.0h2v.s6.a74163c87292 from=seed src=0 shape=acf6bf08 vocab=6d7795b7
-/
lemma equation_zero : W'.Equation ![0, 1, 0] := by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, zero_pow three_ne_zero]

/--
@isnad1 id=iff.0h4v.s6.358a4aa50b09 from=seed src=0 shape=5880de07 vocab=3b0182c0
-/
lemma equation_some (a b : R) : W'.Equation ![a, b, 1] ↔ W'.toAffine.Equation a b := by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]

/--
@isnad1 id=iff.1h3v.s7.11b881168c04 from=seed src=0 shape=ef779b41 vocab=40b587c5
-/
lemma equation_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Equation P ↔ W.toAffine.Equation (P x / P z) (P y / P z) :=
  (equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| equation_some ..

/--
@isnad1 id=eq.2h3v.s6.15c14f276c0b from=seed src=0 shape=ac00e724 vocab=c91c8eed
-/
lemma X_eq_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : P x = 0 :=
  eq_zero_of_pow_eq_zero <| (equation_of_Z_eq_zero hPz).mp hP

/-! ## The nonsingular condition in projective coordinates -/

variable (W') in
/-- The partial derivative `W_X(X, Y, Z)` with respect to `X` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in projective coordinates. -/
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x W'.polynomial

/--
@isnad1 id=eq.0h2v.s10.34d75fe2d8c5 from=seed src=0 shape=a4773bdb vocab=60e70f72
-/
lemma polynomialX_eq : W'.polynomialX =
    C W'.a₁ * Y * Z - (C 3 * X ^ 2 + C (2 * W'.a₂) * X * Z + C W'.a₄ * Z ^ 2) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

/--
@isnad1 id=eq.0h3v.s8.036785e7100d from=seed src=0 shape=4df7427b vocab=93885561
-/
lemma eval_polynomialX (P : Fin 3 → R) : eval P W'.polynomialX =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z + W'.a₄ * P z ^ 2) := by
  rw [polynomialX_eq]
  simp

/--
@isnad1 id=eq.1h3v.s8.4d9301419e54 from=seed src=0 shape=3b9ae472 vocab=75f6b986
-/
lemma eval_polynomialX_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialX / P z ^ 2 = W.toAffine.polynomialX.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomialX, Affine.evalEval_polynomialX]; ring1))
    W.a₁ * P y / P z * div_self hPz - 2 * W.a₂ * P x / P z * div_self hPz
      - W.a₄ * div_self (pow_ne_zero 2 hPz)

variable (W') in
/-- The partial derivative `W_Y(X, Y, Z)` with respect to `Y` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in projective coordinates. -/
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y W'.polynomial

/--
@isnad1 id=eq.0h2v.s10.8c4428bceeb8 from=seed src=0 shape=9cbf67b3 vocab=e1bb703f
-/
lemma polynomialY_eq : W'.polynomialY =
    C 2 * Y * Z + C W'.a₁ * X * Z + C W'.a₃ * Z ^ 2 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

/--
@isnad1 id=eq.0h3v.s8.80697feaac94 from=seed src=0 shape=ff25834f vocab=a0461d23
-/
lemma eval_polynomialY (P : Fin 3 → R) :
    eval P W'.polynomialY = 2 * P y * P z + W'.a₁ * P x * P z + W'.a₃ * P z ^ 2 := by
  rw [polynomialY_eq]
  simp

/--
@isnad1 id=eq.1h3v.s8.3c33802fe4ee from=seed src=0 shape=3b9ae472 vocab=8bf2377a
-/
lemma eval_polynomialY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialY / P z ^ 2 = W.toAffine.polynomialY.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomialY, Affine.evalEval_polynomialY]; ring1))
    2 * P y / P z * div_self hPz + W.a₁ * P x / P z * div_self hPz
      + W.a₃ * div_self (pow_ne_zero 2 hPz)

variable (W') in
/-- The partial derivative `W_Z(X, Y, Z)` with respect to `Z` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in projective coordinates. -/
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z W'.polynomial

/--
@isnad1 id=eq.0h2v.s11.ca5bb90dff6e from=seed src=0 shape=a4fc6069 vocab=3be58a43
-/
lemma polynomialZ_eq : W'.polynomialZ =
    Y ^ 2 + C W'.a₁ * X * Y + C (2 * W'.a₃) * Y * Z
      - (C W'.a₂ * X ^ 2 + C (2 * W'.a₄) * X * Z + C (3 * W'.a₆) * Z ^ 2) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

/--
@isnad1 id=eq.0h3v.s9.8336b4fe0eb2 from=seed src=0 shape=cf19edb3 vocab=472d793c
-/
lemma eval_polynomialZ (P : Fin 3 → R) : eval P W'.polynomialZ =
    P y ^ 2 + W'.a₁ * P x * P y + 2 * W'.a₃ * P y * P z
      - (W'.a₂ * P x ^ 2 + 2 * W'.a₄ * P x * P z + 3 * W'.a₆ * P z ^ 2) := by
  rw [polynomialZ_eq]
  simp

/-- Euler's homogeneous function theorem in projective coordinates.
@isnad1 id=eq.0h3v.s9.d1d48bec1073 from=seed src=0 shape=8a50471e vocab=ebab8b7a
-/
theorem polynomial_relation (P : Fin 3 → R) : 3 * eval P W'.polynomial =
    P x * eval P W'.polynomialX + P y * eval P W'.polynomialY + P z * eval P W'.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

variable (W') in
/-- The proposition that a projective point representative `(x, y, z)` on a Weierstrass curve `W` is
nonsingular.

In other words, either `W_X(x, y, z) ≠ 0`, `W_Y(x, y, z) ≠ 0`, or `W_Z(x, y, z) ≠ 0`.

Note that this definition is only mathematically accurate for fields. -/
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
def Nonsingular (P : Fin 3 → R) : Prop :=
  W'.Equation P ∧
    (eval P W'.polynomialX ≠ 0 ∨ eval P W'.polynomialY ≠ 0 ∨ eval P W'.polynomialZ ≠ 0)

/--
@isnad1 id=iff.0h3v.s10.4bcbc4632fb3 from=seed src=0 shape=f770f423 vocab=4752b35d
-/
lemma nonsingular_iff (P : Fin 3 → R) : W'.Nonsingular P ↔ W'.Equation P ∧
    (W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z + W'.a₄ * P z ^ 2) ≠ 0 ∨
      2 * P y * P z + W'.a₁ * P x * P z + W'.a₃ * P z ^ 2 ≠ 0 ∨
      P y ^ 2 + W'.a₁ * P x * P y + 2 * W'.a₃ * P y * P z
        - (W'.a₂ * P x ^ 2 + 2 * W'.a₄ * P x * P z + 3 * W'.a₆ * P z ^ 2) ≠ 0) := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ]

/--
@isnad1 id=iff.1h4v.s6.c9080e457ccc from=seed src=0 shape=53a15692 vocab=d8dd80da
-/
lemma nonsingular_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) :
    W'.Nonsingular (u • P) ↔ W'.Nonsingular P :=
  have hP {u : R} (hu : IsUnit u) {P : Fin 3 → R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 2 * hP'.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.right⟩
  ⟨hP hu, fun h => hP hu.unit⁻¹.isUnit <| by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

/--
@isnad1 id=iff.0h5v.s5.a4fb18fe0d2c from=seed src=0 shape=d37c1894 vocab=cec5094a
-/
lemma nonsingular_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

/--
@isnad1 id=iff.1h3v.s8.4ace78b2a185 from=seed src=0 shape=c56c65b5 vocab=739bade3
-/
lemma nonsingular_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    W'.Nonsingular P ↔
      W'.Equation P ∧ (3 * P x ^ 2 ≠ 0 ∨ P y ^ 2 + W'.a₁ * P x * P y - W'.a₂ * P x ^ 2 ≠ 0) := by
  simp only [nonsingular_iff, hPz, add_zero, zero_sub, mul_zero,
    zero_pow <| OfNat.ofNat_ne_zero _, neg_ne_zero, ne_self_iff_false, false_or]

/--
@isnad1 id=nonsingu.0h2v.s6.dc063ad35cc1 from=seed src=0 shape=d03dd375 vocab=ba0ddd65
-/
lemma nonsingular_zero [Nontrivial R] : W'.Nonsingular ![0, 1, 0] := by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
  exact fun h => one_ne_zero <| by linear_combination (norm := ring1) h.right

/--
@isnad1 id=iff.0h4v.s6.3053a2ead127 from=seed src=0 shape=5880de07 vocab=40e0ee02
-/
lemma nonsingular_some (a b : R) : W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b := by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h ha hb
  linear_combination (norm := ring1) 3 * h - a * ha - b * hb

/--
@isnad1 id=iff.1h3v.s7.d5430dbe3914 from=seed src=0 shape=ef779b41 vocab=b148c9bf
-/
lemma nonsingular_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.Nonsingular (P x / P z) (P y / P z) :=
  (nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| nonsingular_some ..

/--
@isnad1 id=iff.1h3v.s8.ad64a8a7130f from=seed src=0 shape=ae73bf13 vocab=5e5c1b9f
-/
lemma nonsingular_iff_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.Equation P ∧ (eval P W.polynomialX ≠ 0 ∨ eval P W.polynomialY ≠ 0) := by
  rw [nonsingular_of_Z_ne_zero hPz, Affine.Nonsingular, ← equation_of_Z_ne_zero hPz,
    ← eval_polynomialX_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 2 hPz,
    ← eval_polynomialY_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 2 hPz]

/--
@isnad1 id=ne.2h3v.s6.73ecd4189465 from=seed src=0 shape=ac00e724 vocab=3b83f3c8
-/
lemma Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P y ≠ 0 := by
  intro hPy
  simp only [nonsingular_of_Z_eq_zero hPz, X_eq_zero_of_Z_eq_zero hP.left hPz, hPy, add_zero,
    sub_zero, mul_zero, zero_pow two_ne_zero, or_self, ne_self_iff_false, and_false] at hP

/--
@isnad1 id=isunit.2h3v.s6.742d0896e05d from=seed src=0 shape=00ffb9b8 vocab=35c728c6
-/
lemma isUnit_Y_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y) :=
  (Y_ne_zero_of_Z_eq_zero hP hPz).isUnit

/--
@isnad1 id=equiv.4h4v.s7.a3c10e5f8292 from=seed src=0 shape=dea84912 vocab=58f19f0d
-/
lemma equiv_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  use (isUnit_Y_of_Z_eq_zero hP hPz).unit / (isUnit_Y_of_Z_eq_zero hQ hQz).unit
  simp only [Units.smul_def, smul_fin3, X_eq_zero_of_Z_eq_zero hQ.left hQz, hQz, mul_zero,
    Units.val_div_eq_div_val, IsUnit.unit_spec, (isUnit_Y_of_Z_eq_zero hQ hQz).div_mul_cancel]
  conv_rhs => rw [← fin3_def P, X_eq_zero_of_Z_eq_zero hP.left hPz, hPz]

/--
@isnad1 id=equiv.2h3v.s7.3c05bdee1c21 from=seed src=0 shape=dfd7a0f7 vocab=bc0cac50
-/
lemma equiv_zero_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![0, 1, 0] :=
  equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

/--
@isnad1 id=iff.2h6v.s7.96754259b218 from=seed src=0 shape=ee3a8286 vocab=e66f4028
-/
lemma comp_equiv_comp (f : F →+* K) {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : f ∘ P ≈ f ∘ Q ↔ P ≈ Q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hz : f (P z) = 0
    · exact equiv_of_Z_eq_zero hP hQ ((map_eq_zero_iff f f.injective).mp hz) <|
        (map_eq_zero_iff f f.injective).mp <| (Z_eq_zero_of_equiv h).mp hz
    · refine equiv_of_X_eq_of_Y_eq ((map_ne_zero_iff f f.injective).mp hz)
        ((map_ne_zero_iff f f.injective).mp <| hz.comp (Z_eq_zero_of_equiv h).mpr) ?_ ?_
      all_goals apply f.injective; map_simp
      exacts [X_eq_of_equiv h, Y_eq_of_equiv h]
  · rcases h with ⟨u, rfl⟩
    exact ⟨Units.map f u, (comp_smul ..).symm⟩

variable (W') in
/-- The proposition that a projective point class on a Weierstrass curve `W` is nonsingular.

If `P` is a projective point representative on `W`, then `W.NonsingularLift ⟦P⟧` is definitionally
equivalent to `W.Nonsingular P`.

Note that this definition is only mathematically accurate for fields. -/
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

/--
@isnad1 id=iff.0h3v.s6.fa0e38eead27 from=seed src=0 shape=75c6265f vocab=578bfd8a
-/
lemma nonsingularLift_iff (P : Fin 3 → R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P :=
  Iff.rfl

/--
@isnad1 id=nonsingu.0h2v.s7.a9dcd84d0c82 from=seed src=0 shape=05c67122 vocab=c9c6cf01
-/
lemma nonsingularLift_zero [Nontrivial R] : W'.NonsingularLift ⟦![0, 1, 0]⟧ :=
  nonsingular_zero

/--
@isnad1 id=iff.0h4v.s7.7e16a2eeba6b from=seed src=0 shape=7ae5f2df vocab=ca70c8fb
-/
lemma nonsingularLift_some (a b : R) :
    W'.NonsingularLift ⟦![a, b, 1]⟧ ↔ W'.toAffine.Nonsingular a b :=
  nonsingular_some a b

/-! ## Maps and base changes -/

variable (W') (f : R →+* S)

/-- The Weierstrass curve in projective coordinates mapped over a ring homomorphism `f : R →+* S`.
-/
abbrev map : Projective S :=
  WeierstrassCurve.map W' f

variable (S) in
/-- The Weierstrass curve in projective coordinates base changed to an algebra `S` over `R`. -/
abbrev baseChange [Algebra R S] : Projective S :=
  WeierstrassCurve.baseChange W' S

/-- The notation `\textf` for `WeierstrassCurve.Projective.baseChange W S`. -/
scoped notation:max W:max "⁄" S:max => baseChange W S

/--
@isnad1 id=eq.0h4v.s8.9f14cc3be68a from=seed src=0 shape=688fdc35 vocab=690e5c27
-/
@[simp]
lemma map_polynomial : (W'.map f).polynomial = .map f W'.polynomial := by
  simp only [polynomial]
  map_simp

variable {W'} in
/--
@isnad1 id=equation.1h5v.s6.f23abf584746 from=seed src=0 shape=dd44cecb vocab=cb759d5f
-/
lemma Equation.map {P : Fin 3 → R} (h : W'.Equation P) : (W'.map f).Equation (f ∘ P) := by
  rw [Equation, map_polynomial, eval_map, ← eval₂_comp, h, map_zero]

variable {f} in
/--
@isnad1 id=iff.1h5v.s7.1b563fe394c2 from=seed src=0 shape=bd7fc201 vocab=f8fe8d7a
-/
@[simp]
lemma map_equation (hf : Function.Injective f) (P : Fin 3 → R) :
    (W'.map f).Equation (f ∘ P) ↔ W'.Equation P := by
  simp only [Equation, map_polynomial, eval_map, ← eval₂_comp, map_eq_zero_iff f hf]

/--
@isnad1 id=eq.0h4v.s8.7c3f6f146119 from=seed src=0 shape=688fdc35 vocab=71a26afc
-/
@[simp]
lemma map_polynomialX : (W'.map f).polynomialX = .map f W'.polynomialX := by
  simp only [polynomialX, map_polynomial, pderiv_map]

/--
@isnad1 id=eq.0h4v.s8.3504f8376da6 from=seed src=0 shape=688fdc35 vocab=85a890e6
-/
@[simp]
lemma map_polynomialY : (W'.map f).polynomialY = .map f W'.polynomialY := by
  simp only [polynomialY, map_polynomial, pderiv_map]

/--
@isnad1 id=eq.0h4v.s8.b5df4f4bfc44 from=seed src=0 shape=688fdc35 vocab=fd1a1be4
-/
@[simp]
lemma map_polynomialZ : (W'.map f).polynomialZ = .map f W'.polynomialZ := by
  simp only [polynomialZ, map_polynomial, pderiv_map]

variable {f} in
/--
@isnad1 id=iff.1h5v.s7.2ed4b9543135 from=seed src=0 shape=bd7fc201 vocab=eae68f6e
-/
@[simp]
lemma map_nonsingular (hf : Function.Injective f) (P : Fin 3 → R) :
    (W'.map f).Nonsingular (f ∘ P) ↔ W'.Nonsingular P := by
  simp only [Nonsingular, W'.map_equation hf, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, ← eval₂_comp, map_ne_zero_iff f hf]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B)

/--
@isnad1 id=eq.0h6v.s8.a16d58bcc2bd from=seed src=0 shape=9d6ce88b vocab=34e1adcd
-/
lemma map_baseChange : (W'⁄A).map f = W'⁄B :=
  WeierstrassCurve.map_baseChange W' f

/--
@isnad1 id=eq.0h6v.s8.df405d07089e from=seed src=0 shape=7297a654 vocab=e2da7869
-/
lemma baseChange_polynomial : (W'⁄B).polynomial = .map f (W'⁄A).polynomial := by
  rw [← map_polynomial, map_baseChange]

variable {W'} in
/--
@isnad1 id=equation.1h7v.s8.9821082b2239 from=seed src=0 shape=dd378b05 vocab=cff0e2cf
-/
lemma Equation.baseChange {P : Fin 3 → A} (h : (W'⁄A).Equation P) : (W'⁄B).Equation (f ∘ P) := by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
/--
@isnad1 id=iff.1h7v.s8.727868aa1adc from=seed src=0 shape=a44de2bb vocab=5b624466
-/
lemma baseChange_equation (hf : Function.Injective f) (P : Fin 3 → A) :
    (W'⁄B).Equation (f ∘ P) ↔ (W'⁄A).Equation P := by
  rw [← RingHom.coe_coe, ← map_equation _ hf, AlgHom.toRingHom_eq_coe, map_baseChange]

/--
@isnad1 id=eq.0h6v.s8.fc036787446a from=seed src=0 shape=7297a654 vocab=1c6bc949
-/
lemma baseChange_polynomialX : (W'⁄B).polynomialX = .map f (W'⁄A).polynomialX := by
  rw [← map_polynomialX, map_baseChange]

/--
@isnad1 id=eq.0h6v.s8.1d7890f94eeb from=seed src=0 shape=7297a654 vocab=693a0c81
-/
lemma baseChange_polynomialY : (W'⁄B).polynomialY = .map f (W'⁄A).polynomialY := by
  rw [← map_polynomialY, map_baseChange]

/--
@isnad1 id=eq.0h6v.s8.0f51a2b0be1d from=seed src=0 shape=7297a654 vocab=780bc624
-/
lemma baseChange_polynomialZ : (W'⁄B).polynomialZ = .map f (W'⁄A).polynomialZ := by
  rw [← map_polynomialZ, map_baseChange]

variable {f} in
/--
@isnad1 id=iff.1h7v.s8.8495033845e4 from=seed src=0 shape=a44de2bb vocab=973de1c7
-/
lemma baseChange_nonsingular (hf : Function.Injective f) (P : Fin 3 → A) :
    (W'⁄B).Nonsingular (f ∘ P) ↔ (W'⁄A).Nonsingular P := by
  rw [← RingHom.coe_coe, ← map_nonsingular _ hf, AlgHom.toRingHom_eq_coe, map_baseChange]

end Projective

end WeierstrassCurve
