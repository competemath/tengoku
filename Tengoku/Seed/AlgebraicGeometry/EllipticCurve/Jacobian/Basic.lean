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
# Weierstrass equations and the nonsingular condition in Jacobian coordinates

A point on the projective plane over a commutative ring `R` with weights `(2, 3, 1)` is an
equivalence class `[x : y : z]` of triples `(x, y, z) ≠ (0, 0, 0)` of elements in `R` such that
`(x, y, z) ∼ (x', y', z')` if there is some unit `u` in `Rˣ` with `(x, y, z) = (u²x', u³y', uz')`.

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. A
*Jacobian point* is a point on the projective plane over `R` with weights `(2, 3, 1)` satisfying the
*`(2, 3, 1)`-homogeneous Weierstrass equation* `W(X, Y, Z) = 0` in *Jacobian coordinates*, where
`W(X, Y, Z) := Y² + a₁XYZ + a₃YZ³ - (X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶)`. It is *nonsingular* if its
partial derivatives `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_Z(x, y, z)` do not vanish simultaneously.

This file gives an explicit implementation of equivalence classes of triples up to scaling by
weights, and defines polynomials associated to Weierstrass equations and the nonsingular condition
in Jacobian coordinates. The group law on the actual type of nonsingular Jacobian points will be
defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`, based on the formulae for
group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean`.

## Main definitions

* `WeierstrassCurve.Jacobian.PointClass`: the equivalence class of a point representative.
* `WeierstrassCurve.Jacobian.Nonsingular`: the nonsingular condition on a point representative.
* `WeierstrassCurve.Jacobian.NonsingularLift`: the nonsingular condition on a point class.

## Main statements

* `WeierstrassCurve.Jacobian.polynomial_relation`: Euler's homogeneous function theorem.

## Implementation notes

All definitions and lemmas for Weierstrass curves in Jacobian coordinates live in the namespace
`WeierstrassCurve.Jacobian` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toJacobian`. This
can be converted into `WeierstrassCurve.Affine` using `WeierstrassCurve.Jacobian.toAffine`.

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not syntactically equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not syntactically equal to `![u² * Q x, u³ * Q y, u * Q z]`, so the
lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms. Files in
`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian` make extensive use of `erw` to get around this.
While `erw` is often an indication of a problem, in this case it is self-contained and should not
cause any issues. It would alternatively be possible to add some automation to assist here.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, Weierstrass equation, nonsingular
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

/-! ## Jacobian coordinates -/

variable (R) in
/-- An abbreviation for a Weierstrass curve in Jacobian coordinates. -/
abbrev Jacobian : Type r :=
  WeierstrassCurve R

/-- The conversion from a Weierstrass curve to Jacobian coordinates. -/
abbrev toJacobian (W : WeierstrassCurve R) : Jacobian R :=
  W

namespace Jacobian

/-- The conversion from a Weierstrass curve in Jacobian coordinates to affine coordinates. -/
abbrev toAffine (W' : Jacobian R) : Affine R :=
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

variable [CommRing R] [Field F] {W' : Jacobian R} {W : Jacobian F} {S : Type s} [CommRing S]
  {A : Type u} [CommRing A] {B : Type v} [CommRing B] {K : Type v} [Field K]

/-- The scalar multiplication for a Jacobian point representative on a Weierstrass curve. -/
scoped instance : SMul R <| Fin 3 → R :=
  ⟨fun u P => ![u ^ 2 * P x, u ^ 3 * P y, u * P z]⟩

/--
@isnad1 id=eq.0h3v.s7.19fe208e26c1 from=seed src=0 shape=9aa2ef55 vocab=5596b018
-/
lemma smul_fin3 (P : Fin 3 → R) (u : R) : u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z] :=
  rfl

/--
@isnad1 id=and.0h3v.s8.6edcf7782f71 from=seed src=0 shape=2f5ae71d vocab=d45a67b3
-/
lemma smul_fin3_ext (P : Fin 3 → R) (u : R) :
    (u • P) x = u ^ 2 * P x ∧ (u • P) y = u ^ 3 * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩

/--
@isnad1 id=eq.0h5v.s7.6e60a0a3bff2 from=seed src=0 shape=eb8e3ac3 vocab=ffdce5f9
-/
lemma comp_smul (f : R →+* S) (P : Fin 3 → R) (u : R) : f ∘ (u • P) = f u • f ∘ P := by
  ext n; fin_cases n <;> simp only [smul_fin3, comp_fin3] <;> map_simp

/-- The multiplicative action for a Jacobian point representative on a Weierstrass curve. -/
scoped instance : MulAction R <| Fin 3 → R where
  one_smul _ := by simp only [smul_fin3, one_pow, one_mul, fin3_def]
  mul_smul _ _ _ := by simp only [smul_fin3, mul_pow, mul_assoc, fin3_def_ext]

/-- The equivalence setoid for a Jacobian point representative on a Weierstrass curve. -/
@[reducible]
scoped instance : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

variable (R) in
/-- The equivalence class of a Jacobian point representative on a Weierstrass curve. -/
abbrev PointClass : Type r :=
  MulAction.orbitRel.Quotient Rˣ <| Fin 3 → R

/--
@isnad1 id=equiv.1h3v.s6.ff4a9f694ebd from=seed src=0 shape=3d19466f vocab=1633e5a0
-/
lemma smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : u • P ≈ P :=
  ⟨hu.unit, rfl⟩

/--
@isnad1 id=eq.1h3v.s7.9e4d5d0c3375 from=seed src=0 shape=85116117 vocab=c2d900ea
-/
@[simp]
lemma smul_eq (P : Fin 3 → R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
  Quotient.eq.mpr <| smul_equiv P hu

/--
@isnad1 id=iff.2h5v.s7.246770b3dd7f from=seed src=0 shape=d6f15e0f vocab=1633e5a0
-/
lemma smul_equiv_smul (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    u • P ≈ v • Q ↔ P ≈ Q := by
  rw [← Quotient.eq_iff_equiv, ← Quotient.eq_iff_equiv, smul_eq P hu, smul_eq Q hv]

/--
@isnad1 id=iff.2h3v.s7.7766086a4b3d from=seed src=0 shape=8ffaa130 vocab=f5183812
-/
lemma equiv_iff_eq_of_Z_eq' {P Q : Fin 3 → R} (hz : P z = Q z) (hQz : Q z ∈ nonZeroDivisors R) :
    P ≈ Q ↔ P = Q := by
  refine ⟨?_, Quotient.exact.comp <| congrArg _⟩
  rintro ⟨u, rfl⟩
  simp only [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors hQz).mp <| one_mul (Q z) ▸ hz]
  rw [one_smul]

/--
@isnad1 id=iff.2h3v.s7.37a292f3429b from=seed src=0 shape=7940b1a1 vocab=e9c08e67
-/
lemma equiv_iff_eq_of_Z_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hz : P z = Q z) (hQz : Q z ≠ 0) :
    P ≈ Q ↔ P = Q :=
  equiv_iff_eq_of_Z_eq' hz <| mem_nonZeroDivisors_of_ne_zero hQz

/--
@isnad1 id=iff.0h4v.s6.388228271262 from=seed src=0 shape=3fbb5afd vocab=796d72be
-/
lemma Z_eq_zero_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨_, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext, Units.mul_right_eq_zero]

/--
@isnad1 id=eq.0h4v.s7.c1fa2e5de911 from=seed src=0 shape=1463b43d vocab=ccb47f87
-/
lemma X_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P x * Q z ^ 2 = Q x * P z ^ 2 := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

/--
@isnad1 id=eq.0h4v.s7.b6a2e049efac from=seed src=0 shape=1463b43d vocab=ccb47f87
-/
lemma Y_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P y * Q z ^ 3 = Q y * P z ^ 3 := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

/--
@isnad1 id=not.2h3v.s6.e8c36eb95083 from=seed src=0 shape=cdf86fe4 vocab=796d72be
-/
lemma not_equiv_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) (hQz : Q z ≠ 0) : ¬P ≈ Q :=
  fun h => hQz <| (Z_eq_zero_of_equiv h).mp hPz

/--
@isnad1 id=not.2h3v.s6.4ae11e0c1702 from=seed src=0 shape=cdf86fe4 vocab=796d72be
-/
lemma not_equiv_of_Z_eq_zero_right {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z = 0) : ¬P ≈ Q :=
  fun h => hPz <| (Z_eq_zero_of_equiv h).mpr hQz

/--
@isnad1 id=not.1h3v.s7.9eb00541b85b from=seed src=0 shape=44b921bc vocab=ccb47f87
-/
lemma not_equiv_of_X_ne {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : ¬P ≈ Q :=
  hx.comp X_eq_of_equiv

/--
@isnad1 id=not.1h3v.s7.0d5731e3ef7a from=seed src=0 shape=44b921bc vocab=ccb47f87
-/
lemma not_equiv_of_Y_ne {P Q : Fin 3 → R} (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : ¬P ≈ Q :=
  hy.comp Y_eq_of_equiv

/--
@isnad1 id=equiv.4h3v.s8.2e4d56b34427 from=seed src=0 shape=2297ae1a vocab=84532aa4
-/
lemma equiv_of_X_eq_of_Y_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3) : P ≈ Q := by
  use Units.mk0 _ hPz / Units.mk0 _ hQz
  simp only [Units.smul_def, smul_fin3, Units.val_div_eq_div_val, Units.val_mk0, div_pow, mul_comm,
    mul_div, ← hx, ← hy, mul_div_cancel_right₀ _ <| pow_ne_zero _ hQz, mul_div_cancel_right₀ _ hQz,
    fin3_def]

/--
@isnad1 id=equiv.1h2v.s8.e74d0006add0 from=seed src=0 shape=9a66aa73 vocab=0215c1cb
-/
lemma equiv_some_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    P ≈ ![P x / P z ^ 2, P y / P z ^ 3, 1] :=
  equiv_of_X_eq_of_Y_eq hPz one_ne_zero
    (by linear_combination (norm := (matrix_simp; ring1)) -P x * div_self (pow_ne_zero 2 hPz))
    (by linear_combination (norm := (matrix_simp; ring1)) -P y * div_self (pow_ne_zero 3 hPz))

/--
@isnad1 id=iff.2h3v.s8.07f4874889f3 from=seed src=0 shape=6fb28c99 vocab=7bd3ae48
-/
lemma X_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P x * Q z ^ 2 = Q x * P z ^ 2 ↔ P x / P z ^ 2 = Q x / Q z ^ 2 :=
  (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).symm

/--
@isnad1 id=iff.2h3v.s8.4b8ebf879d6a from=seed src=0 shape=6fb28c99 vocab=7bd3ae48
-/
lemma Y_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z ^ 3 = Q y * P z ^ 3 ↔ P y / P z ^ 3 = Q y / Q z ^ 3 :=
  (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)).symm

/-! ## Weierstrass equations in Jacobian coordinates -/

variable (W') in
/-- The polynomial `W(X, Y, Z) := Y² + a₁XYZ + a₃YZ³ - (X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶)` associated to a
Weierstrass curve `W` over a ring `R` in Jacobian coordinates.

This is represented as a term of type `MvPolynomial (Fin 3) R`, where `X`, `Y`, and `Z`
represent `X`, `Y`, and `Z` respectively. -/
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  Y ^ 2 + C W'.a₁ * X * Y * Z + C W'.a₃ * Y * Z ^ 3
    - (X ^ 3 + C W'.a₂ * X ^ 2 * Z ^ 2 + C W'.a₄ * X * Z ^ 4 + C W'.a₆ * Z ^ 6)

/--
@isnad1 id=eq.0h3v.s9.221fd1c15cea from=seed src=0 shape=905d0870 vocab=3e1e5c3c
-/
lemma eval_polynomial (P : Fin 3 → R) : eval P W'.polynomial =
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) := by
  rw [polynomial]
  simp

/--
@isnad1 id=eq.1h3v.s8.03e966e28f12 from=seed src=0 shape=ec8da07d vocab=c1a36c8d
-/
lemma eval_polynomial_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : eval P W.polynomial / P z ^ 6 =
    W.toAffine.polynomial.evalEval (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [eval_polynomial, Affine.evalEval_polynomial]; ring1))
    W.a₁ * P x * P y / P z ^ 5 * div_self hPz + W.a₃ * P y / P z ^ 3 * div_self (pow_ne_zero 3 hPz)
      - W.a₂ * P x ^ 2 / P z ^ 4 * div_self (pow_ne_zero 2 hPz)
      - W.a₄ * P x / P z ^ 2 * div_self (pow_ne_zero 4 hPz) - W.a₆ * div_self (pow_ne_zero 6 hPz)

variable (W') in
/-- The proposition that a Jacobian point representative `(x, y, z)` lies in a Weierstrass curve
`W`.

In other words, it satisfies the `(2, 3, 1)`-homogeneous Weierstrass equation `W(X, Y, Z) = 0`. -/
def Equation (P : Fin 3 → R) : Prop :=
  eval P W'.polynomial = 0

/--
@isnad1 id=iff.0h3v.s9.0bda587fbbba from=seed src=0 shape=86661d5a vocab=6c781f7e
-/
lemma equation_iff (P : Fin 3 → R) : W'.Equation P ↔
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) = 0 := by
  rw [Equation, eval_polynomial]

/--
@isnad1 id=iff.1h4v.s6.f2a30a746f61 from=seed src=0 shape=53a15692 vocab=b2633cf6
-/
lemma equation_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P :=
  have hP (u : R) {P : Fin 3 → R} (hP : W'.Equation P) : W'.Equation <| u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 6 * hP
  ⟨fun h => by convert! hP (↑hu.unit⁻¹) h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩

/--
@isnad1 id=iff.0h5v.s5.aff3abd6a352 from=seed src=0 shape=d37c1894 vocab=e889511d
-/
lemma equation_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

/--
@isnad1 id=iff.1h3v.s7.c84a0b665ed2 from=seed src=0 shape=5fe3784c vocab=2b5c89b0
-/
lemma equation_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    W'.Equation P ↔ P y ^ 2 = P x ^ 3 := by
  simp only [equation_iff, hPz, add_zero, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _, sub_eq_zero]

/--
@isnad1 id=equation.0h2v.s6.7084fad988fe from=seed src=0 shape=acf6bf08 vocab=53f8c94b
-/
lemma equation_zero : W'.Equation ![1, 1, 0] := by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, one_pow]

/--
@isnad1 id=iff.0h4v.s6.b80d236f8699 from=seed src=0 shape=5880de07 vocab=a652718e
-/
lemma equation_some (a b : R) : W'.Equation ![a, b, 1] ↔ W'.toAffine.Equation a b := by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]

/--
@isnad1 id=iff.1h3v.s7.68e143540cac from=seed src=0 shape=ffe8a7ed vocab=537d3270
-/
lemma equation_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Equation P ↔ W.toAffine.Equation (P x / P z ^ 2) (P y / P z ^ 3) :=
  (equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| equation_some ..

/-! ## The nonsingular condition in Jacobian coordinates -/

variable (W') in
/-- The partial derivative `W_X(X, Y, Z)` with respect to `X` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x W'.polynomial

/--
@isnad1 id=eq.0h2v.s10.84f8f55388ad from=seed src=0 shape=b9b2ff5b vocab=bacc164d
-/
lemma polynomialX_eq : W'.polynomialX =
    C W'.a₁ * Y * Z - (C 3 * X ^ 2 + C (2 * W'.a₂) * X * Z ^ 2 + C W'.a₄ * Z ^ 4) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

/--
@isnad1 id=eq.0h3v.s9.5223e733c923 from=seed src=0 shape=ebee2dcb vocab=d2a0a4a3
-/
lemma eval_polynomialX (P : Fin 3 → R) : eval P W'.polynomialX =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) := by
  rw [polynomialX_eq]
  simp

/--
@isnad1 id=eq.1h3v.s8.1ce1de27a2e3 from=seed src=0 shape=ec8da07d vocab=35de5a36
-/
lemma eval_polynomialX_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialX / P z ^ 4 =
      W.toAffine.polynomialX.evalEval (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [eval_polynomialX, Affine.evalEval_polynomialX]; ring1))
    W.a₁ * P y / P z ^ 3 * div_self hPz - 2 * W.a₂ * P x / P z ^ 2 * div_self (pow_ne_zero 2 hPz)
      - W.a₄ * div_self (pow_ne_zero 4 hPz)

variable (W') in
/-- The partial derivative `W_Y(X, Y, Z)` with respect to `Y` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y W'.polynomial

/--
@isnad1 id=eq.0h2v.s10.d49f1884006c from=seed src=0 shape=1af2f395 vocab=650a589c
-/
lemma polynomialY_eq : W'.polynomialY = C 2 * Y + C W'.a₁ * X * Z + C W'.a₃ * Z ^ 3 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

/--
@isnad1 id=eq.0h3v.s8.b55841f2f628 from=seed src=0 shape=06739eb8 vocab=77eeaf6d
-/
lemma eval_polynomialY (P : Fin 3 → R) :
    eval P W'.polynomialY = 2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3 := by
  rw [polynomialY_eq]
  simp

/--
@isnad1 id=eq.1h3v.s8.7bc885398f3c from=seed src=0 shape=ec8da07d vocab=fd0143c5
-/
lemma eval_polynomialY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialY / P z ^ 3 =
      W.toAffine.polynomialY.evalEval (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [eval_polynomialY, Affine.evalEval_polynomialY]; ring1))
    W.a₁ * P x / P z ^ 2 * div_self hPz + W.a₃ * div_self (pow_ne_zero 3 hPz)

variable (W') in
/-- The partial derivative `W_Z(X, Y, Z)` with respect to `Z` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z W'.polynomial

/--
@isnad1 id=eq.0h2v.s11.01f56016d751 from=seed src=0 shape=f3226679 vocab=8bd2e5e5
-/
lemma polynomialZ_eq : W'.polynomialZ = C W'.a₁ * X * Y + C (3 * W'.a₃) * Y * Z ^ 2 -
    (C (2 * W'.a₂) * X ^ 2 * Z + C (4 * W'.a₄) * X * Z ^ 3 + C (6 * W'.a₆) * Z ^ 5) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

/--
@isnad1 id=eq.0h3v.s9.ce76c84c090d from=seed src=0 shape=87355f78 vocab=42230a05
-/
lemma eval_polynomialZ (P : Fin 3 → R) : eval P W'.polynomialZ =
    W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2 -
      (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 + 6 * W'.a₆ * P z ^ 5) := by
  rw [polynomialZ_eq]
  simp

/-- Euler's homogeneous function theorem in Jacobian coordinates.
@isnad1 id=eq.0h3v.s9.f94e128175b3 from=seed src=0 shape=8c0aedf6 vocab=2ff6e0a8
-/
theorem polynomial_relation (P : Fin 3 → R) : 6 * eval P W'.polynomial =
    2 * P x * eval P W'.polynomialX + 3 * P y * eval P W'.polynomialY +
      P z * eval P W'.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

variable (W') in
/-- The proposition that a Jacobian point representative `(x, y, z)` on a Weierstrass curve `W` is
nonsingular.

In other words, either `W_X(x, y, z) ≠ 0`, `W_Y(x, y, z) ≠ 0`, or `W_Z(x, y, z) ≠ 0`.

Note that this definition is only mathematically accurate for fields. -/
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
def Nonsingular (P : Fin 3 → R) : Prop :=
  W'.Equation P ∧
    (eval P W'.polynomialX ≠ 0 ∨ eval P W'.polynomialY ≠ 0 ∨ eval P W'.polynomialZ ≠ 0)

/--
@isnad1 id=iff.0h3v.s10.fd6f3a24dcef from=seed src=0 shape=40fc1bc6 vocab=f1c57eab
-/
lemma nonsingular_iff (P : Fin 3 → R) : W'.Nonsingular P ↔ W'.Equation P ∧
    (W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) ≠ 0 ∨
      2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3 ≠ 0 ∨
      W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2
        - (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 + 6 * W'.a₆ * P z ^ 5) ≠ 0) := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ]

/--
@isnad1 id=iff.1h4v.s6.b1482ad592c8 from=seed src=0 shape=53a15692 vocab=558a140a
-/
lemma nonsingular_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) :
    W'.Nonsingular (u • P) ↔ W'.Nonsingular P :=
  have hP {u : R} (hu : IsUnit u) {P : Fin 3 → R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 4 * hP'.left,
      by linear_combination (norm := ring1) u ^ 3 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 5 * hP'.right.right⟩
  ⟨hP hu, fun h => hP hu.unit⁻¹.isUnit <| by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

/--
@isnad1 id=iff.0h5v.s5.54deaa77115c from=seed src=0 shape=d37c1894 vocab=a7a268e5
-/
lemma nonsingular_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

/--
@isnad1 id=iff.1h3v.s8.eb27f59d7e9a from=seed src=0 shape=d21c16c9 vocab=e491e333
-/
lemma nonsingular_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    W'.Nonsingular P ↔ W'.Equation P ∧ (3 * P x ^ 2 ≠ 0 ∨ 2 * P y ≠ 0 ∨ W'.a₁ * P x * P y ≠ 0) := by
  simp only [nonsingular_iff, hPz, add_zero, sub_zero, zero_sub, mul_zero,
    zero_pow <| OfNat.ofNat_ne_zero _, neg_ne_zero]

/--
@isnad1 id=nonsingu.0h2v.s6.e17b5fd4e58d from=seed src=0 shape=d03dd375 vocab=8988b824
-/
lemma nonsingular_zero [Nontrivial R] : W'.Nonsingular ![1, 1, 0] := by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
  exact fun h => one_ne_zero <| by linear_combination (norm := ring1) h.1 - h.2.1

/--
@isnad1 id=iff.0h4v.s6.3eebb679467a from=seed src=0 shape=5880de07 vocab=41ae95d9
-/
lemma nonsingular_some (a b : R) : W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b := by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h ha hb
  linear_combination (norm := ring1) 6 * h - 2 * a * ha - 3 * b * hb

/--
@isnad1 id=iff.1h3v.s7.4f4cdddfabca from=seed src=0 shape=ffe8a7ed vocab=38f1f40c
-/
lemma nonsingular_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.Nonsingular (P x / P z ^ 2) (P y / P z ^ 3) :=
  (nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| nonsingular_some ..

/--
@isnad1 id=iff.1h3v.s8.d49487a8fd14 from=seed src=0 shape=ae73bf13 vocab=587d6819
-/
lemma nonsingular_iff_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.Equation P ∧ (eval P W.polynomialX ≠ 0 ∨ eval P W.polynomialY ≠ 0) := by
  rw [nonsingular_of_Z_ne_zero hPz, Affine.Nonsingular, ← equation_of_Z_ne_zero hPz,
    ← eval_polynomialX_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 4 hPz,
    ← eval_polynomialY_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 3 hPz]

/--
@isnad1 id=ne.2h3v.s6.de3daa07c52c from=seed src=0 shape=ac00e724 vocab=3026de82
-/
lemma X_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P x ≠ 0 := by
  intro hPx
  simp only [nonsingular_of_Z_eq_zero hPz, equation_of_Z_eq_zero hPz, hPx, mul_zero, zero_mul,
    zero_pow <| OfNat.ofNat_ne_zero _, ne_self_iff_false, or_false, false_or] at hP
  rwa [pow_eq_zero_iff two_ne_zero, hP.left, eq_self, true_and, mul_zero, ne_self_iff_false] at hP

/--
@isnad1 id=isunit.2h3v.s6.b5bf284822d1 from=seed src=0 shape=00ffb9b8 vocab=84e2b4e3
-/
lemma isUnit_X_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x) :=
  (X_ne_zero_of_Z_eq_zero hP hPz).isUnit

/--
@isnad1 id=ne.2h3v.s6.9804666cc987 from=seed src=0 shape=ac00e724 vocab=3026de82
-/
lemma Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P y ≠ 0 := by
  have hPx : P x ≠ 0 := X_ne_zero_of_Z_eq_zero hP hPz
  intro hPy
  rw [nonsingular_of_Z_eq_zero hPz, equation_of_Z_eq_zero hPz, hPy, zero_pow two_ne_zero] at hP
  exact hPx <| eq_zero_of_pow_eq_zero hP.left.symm

/--
@isnad1 id=isunit.2h3v.s6.08d2cc56d9fd from=seed src=0 shape=00ffb9b8 vocab=84e2b4e3
-/
lemma isUnit_Y_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y) :=
  (Y_ne_zero_of_Z_eq_zero hP hPz).isUnit

/--
@isnad1 id=equiv.4h4v.s7.338990930966 from=seed src=0 shape=dea84912 vocab=b3167e72
-/
lemma equiv_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  have hPx : IsUnit <| P x := isUnit_X_of_Z_eq_zero hP hPz
  have hPy : IsUnit <| P y := isUnit_Y_of_Z_eq_zero hP hPz
  have hQx : IsUnit <| Q x := isUnit_X_of_Z_eq_zero hQ hQz
  have hQy : IsUnit <| Q y := isUnit_Y_of_Z_eq_zero hQ hQz
  simp only [nonsingular_of_Z_eq_zero, equation_of_Z_eq_zero, hPz, hQz] at hP hQ
  use (hPy.unit / hPx.unit) * (hQx.unit / hQy.unit)
  simp only [Units.smul_def, smul_fin3, Units.val_mul, Units.val_div_eq_div_val, IsUnit.unit_spec,
    mul_pow, div_pow, hQz, mul_zero]
  conv_rhs => rw [← fin3_def P, hPz]
  congr! 2
  · rw [hP.left, pow_succ, (hPx.pow 2).mul_div_cancel_left, hQ.left, pow_succ _ 2,
      (hQx.pow 2).div_mul_cancel_left, hQx.inv_mul_cancel_right]
  · rw [← hP.left, pow_succ, (hPy.pow 2).mul_div_cancel_left, ← hQ.left, pow_succ _ 2,
      (hQy.pow 2).div_mul_cancel_left, hQy.inv_mul_cancel_right]

/--
@isnad1 id=equiv.2h3v.s7.e104ec027e33 from=seed src=0 shape=dfd7a0f7 vocab=8db06e24
-/
lemma equiv_zero_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![1, 1, 0] :=
  equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

/--
@isnad1 id=iff.2h6v.s7.b2dc3fbfaae6 from=seed src=0 shape=ee3a8286 vocab=dd8120cd
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
/-- The proposition that a Jacobian point class on a Weierstrass curve `W` is nonsingular.

If `P` is a Jacobian point representative on `W`, then `W.NonsingularLift ⟦P⟧` is definitionally
equivalent to `W.Nonsingular P`.

Note that this definition is only mathematically accurate for fields. -/
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

/--
@isnad1 id=iff.0h3v.s6.82acce0a9e04 from=seed src=0 shape=75c6265f vocab=b9071654
-/
lemma nonsingularLift_iff (P : Fin 3 → R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P :=
  Iff.rfl

/--
@isnad1 id=nonsingu.0h2v.s7.7eaf61effcea from=seed src=0 shape=05c67122 vocab=d5d8f733
-/
lemma nonsingularLift_zero [Nontrivial R] : W'.NonsingularLift ⟦![1, 1, 0]⟧ :=
  nonsingular_zero

/--
@isnad1 id=iff.0h4v.s6.a49d7f14c633 from=seed src=0 shape=7ae5f2df vocab=17dd586f
-/
lemma nonsingularLift_some (a b : R) :
    W'.NonsingularLift ⟦![a, b, 1]⟧ ↔ W'.toAffine.Nonsingular a b :=
  nonsingular_some a b

/-! ## Maps and base changes -/

variable (W') (f : R →+* S)

/-- The Weierstrass curve in Jacobian coordinates mapped over a ring homomorphism `f : R →+* S`. -/
abbrev map : Jacobian S :=
  WeierstrassCurve.map W' f

variable (S) in
/-- The Weierstrass curve in Jacobian coordinates base changed to an algebra `S` over `R`. -/
abbrev baseChange [Algebra R S] : Jacobian S :=
  WeierstrassCurve.baseChange W' S

/-- The notation `\textf` for `WeierstrassCurve.Jacobian.baseChange W S`. -/
scoped notation:max W:max "⁄" S:max => baseChange W S

/--
@isnad1 id=eq.0h4v.s8.b90a43d9f575 from=seed src=0 shape=688fdc35 vocab=427f591f
-/
@[simp]
lemma map_polynomial : (W'.map f).polynomial = .map f W'.polynomial := by
  simp only [polynomial]
  map_simp

variable {W'} in
/--
@isnad1 id=equation.1h5v.s6.46551d23e79a from=seed src=0 shape=dd44cecb vocab=940ce47e
-/
lemma Equation.map {P : Fin 3 → R} (h : W'.Equation P) : (W'.map f).Equation (f ∘ P) := by
  rw [Equation, map_polynomial, eval_map, ← eval₂_comp, h, map_zero]

variable {f} in
/--
@isnad1 id=iff.1h5v.s7.b8f84f1b5680 from=seed src=0 shape=bd7fc201 vocab=67052193
-/
@[simp]
lemma map_equation (hf : Function.Injective f) (P : Fin 3 → R) :
    (W'.map f).Equation (f ∘ P) ↔ W'.Equation P := by
  simp only [Equation, map_polynomial, eval_map, ← eval₂_comp, map_eq_zero_iff f hf]

/--
@isnad1 id=eq.0h4v.s8.e5d341dc0b71 from=seed src=0 shape=688fdc35 vocab=9af1366a
-/
@[simp]
lemma map_polynomialX : (W'.map f).polynomialX = .map f W'.polynomialX := by
  simp only [polynomialX, map_polynomial, pderiv_map]

/--
@isnad1 id=eq.0h4v.s8.892cf2c4ae77 from=seed src=0 shape=688fdc35 vocab=0eb09cfd
-/
@[simp]
lemma map_polynomialY : (W'.map f).polynomialY = .map f W'.polynomialY := by
  simp only [polynomialY, map_polynomial, pderiv_map]

/--
@isnad1 id=eq.0h4v.s8.d437655e8e8c from=seed src=0 shape=688fdc35 vocab=7e4b0e89
-/
@[simp]
lemma map_polynomialZ : (W'.map f).polynomialZ = .map f W'.polynomialZ := by
  simp only [polynomialZ, map_polynomial, pderiv_map]

variable {f} in
/--
@isnad1 id=iff.1h5v.s7.ed7975bea601 from=seed src=0 shape=bd7fc201 vocab=4ed16a03
-/
@[simp]
lemma map_nonsingular (hf : Function.Injective f) (P : Fin 3 → R) :
    (W'.map f).Nonsingular (f ∘ P) ↔ W'.Nonsingular P := by
  simp only [Nonsingular, W'.map_equation hf, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, ← eval₂_comp, map_ne_zero_iff f hf]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B)

/--
@isnad1 id=eq.0h6v.s8.4d9ccf9fced7 from=seed src=0 shape=9d6ce88b vocab=45ba8a3f
-/
lemma map_baseChange : (W'⁄A).map f = W'⁄B :=
  WeierstrassCurve.map_baseChange W' f

/--
@isnad1 id=eq.0h6v.s8.f04446e06f00 from=seed src=0 shape=7297a654 vocab=aac4d064
-/
lemma baseChange_polynomial : (W'⁄B).polynomial = .map f (W'⁄A).polynomial := by
  rw [← map_polynomial, map_baseChange]

variable {W'} in
/--
@isnad1 id=equation.1h7v.s8.66cdd7a6cb65 from=seed src=0 shape=dd378b05 vocab=fca61883
-/
lemma Equation.baseChange {P : Fin 3 → A} (h : (W'⁄A).Equation P) : (W'⁄B).Equation (f ∘ P) := by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
/--
@isnad1 id=iff.1h7v.s8.bcc55b640a75 from=seed src=0 shape=a44de2bb vocab=ea514bb6
-/
lemma baseChange_equation (hf : Function.Injective f) (P : Fin 3 → A) :
    (W'⁄B).Equation (f ∘ P) ↔ (W'⁄A).Equation P := by
  rw [← RingHom.coe_coe, ← map_equation _ hf, AlgHom.toRingHom_eq_coe, map_baseChange]

/--
@isnad1 id=eq.0h6v.s8.91cfd72e852e from=seed src=0 shape=7297a654 vocab=59f733db
-/
lemma baseChange_polynomialX : (W'⁄B).polynomialX = .map f (W'⁄A).polynomialX := by
  rw [← map_polynomialX, map_baseChange]

/--
@isnad1 id=eq.0h6v.s8.cf7b7d1cfbaa from=seed src=0 shape=7297a654 vocab=518994c6
-/
lemma baseChange_polynomialY : (W'⁄B).polynomialY = .map f (W'⁄A).polynomialY := by
  rw [← map_polynomialY, map_baseChange]

/--
@isnad1 id=eq.0h6v.s8.a206b7148a17 from=seed src=0 shape=7297a654 vocab=fdb21e56
-/
lemma baseChange_polynomialZ : (W'⁄B).polynomialZ = .map f (W'⁄A).polynomialZ := by
  rw [← map_polynomialZ, map_baseChange]

variable {f} in
/--
@isnad1 id=iff.1h7v.s8.dfd6d4752b6f from=seed src=0 shape=a44de2bb vocab=0c006a61
-/
lemma baseChange_nonsingular (hf : Function.Injective f) (P : Fin 3 → A) :
    (W'⁄B).Nonsingular (f ∘ P) ↔ (W'⁄A).Nonsingular P := by
  rw [← RingHom.coe_coe, ← map_nonsingular _ hf, AlgHom.toRingHom_eq_coe, map_baseChange]

end Jacobian

end WeierstrassCurve
