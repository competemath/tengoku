/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Order
public import Tengoku.Tauceti.TauCeti.FieldTheory.FunctionField.Place.Degree

/-!
# Divisors of an algebraic function field

A divisor of `F / k` is a finite integer combination of its normalized places.  The underlying
free abelian group, its coefficientwise order, effectivity, and its positive/negative part
decomposition are supplied by `TauCeti.AlgebraicGeometry.WeilDivisor`; this file specializes that
API rather than constructing a second formal-divisor theory.

The degree of a function-field divisor is the weighted degree

`\sum_P D(P) [F_P : k]`.

The residue degrees are finite and positive when `F / k` is an algebraic function field.  Thus
degree is nonnegative on effective divisors, and is positive on every nonzero effective divisor.
The weights cannot be omitted over a general constant field: this file identifies the weighted
degree with the unweighted coefficient sum only when every place is rational, in particular over
an algebraically closed constant field.

This is the divisor carrier and degree portion of Stichtenoth, *Algebraic Function Fields and
Codes*, 2nd ed., Definition 1.4.1.  Principal divisors and the product formula follow after the
finiteness of zeros and poles.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable (k F : Type*) [Field k] [Field F] [Algebra k F]

/-- A divisor of `F / k` is a finite formal integer combination of its normalized places. -/
abbrev Divisor :=
  WeilDivisor (Place k F)

namespace Divisor

variable {k F}

/-- The degree of a function-field divisor, weighted by the degrees of its residue fields. -/
noncomputable def degree : Divisor k F →+ ℤ :=
  WeilDivisor.weightedDegree fun P => P.degree

/-- The degree is the finite sum of each coefficient times the corresponding residue degree. -/
lemma degree_apply (D : Divisor k F) :
    degree D = D.sum fun P n => n * P.degree := by
  simpa only [degree] using
    WeilDivisor.weightedDegree_apply (fun P : Place k F => (P.degree : ℤ)) D

@[simp]
lemma degree_zero : degree (0 : Divisor k F) = 0 :=
  map_zero degree

@[simp]
lemma degree_add (D E : Divisor k F) : degree (D + E) = degree D + degree E :=
  map_add degree D E

@[simp]
lemma degree_neg (D : Divisor k F) : degree (-D) = -degree D :=
  map_neg degree D

@[simp]
lemma degree_sub (D E : Divisor k F) : degree (D - E) = degree D - degree E :=
  map_sub degree D E

@[simp]
lemma degree_zsmul (n : ℤ) (D : Divisor k F) : degree (n • D) = n * degree D := by
  simpa only [smul_eq_mul] using map_zsmul degree n D

/-- A place viewed as a prime divisor has degree equal to its residue degree. -/
@[simp]
lemma degree_ofPoint (P : Place k F) : degree (WeilDivisor.ofPoint P) = P.degree := by
  simpa only [degree] using
    WeilDivisor.weightedDegree_ofPoint (fun Q : Place k F => (Q.degree : ℤ)) P

/-- The degree of a divisor supported at one place. -/
@[simp]
lemma degree_single (P : Place k F) (n : ℤ) :
    degree (Finsupp.single P n) = n * P.degree := by
  rw [WeilDivisor.single_eq_zsmul_ofPoint, degree_zsmul, degree_ofPoint]

/-- The degree of an effective divisor is nonnegative.  This does not need a function-field
hypothesis, since `finrank` is always a natural number even before its finiteness is known. -/
lemma degree_nonneg {D : Divisor k F} (hD : 0 ≤ D) : 0 ≤ degree D := by
  have hD' : WeilDivisor.IsEffective D := WeilDivisor.isEffective_iff_zero_le.mpr hD
  simpa only [degree] using
    hD'.weightedDegree_nonneg fun P : Place k F => Int.natCast_nonneg P.degree

/-- Residue-degree weighting is monotone for the coefficientwise order on divisors. -/
lemma degree_le_of_le {D E : Divisor k F} (hDE : D ≤ E) : degree D ≤ degree E := by
  simpa only [degree] using WeilDivisor.weightedDegree_le_of_le
    (fun P : Place k F => Int.natCast_nonneg P.degree) hDE

private lemma degree_pos_of_isFunctionField (hF : IsFunctionField k F) (P : Place k F) :
    0 < (P.degree : ℤ) := by
  exact_mod_cast P.one_le_degree_of_isFunctionField hF

/-- An effective divisor of a function field has degree zero exactly when it is zero. -/
lemma degree_eq_zero_iff (hF : IsFunctionField k F) {D : Divisor k F} (hD : 0 ≤ D) :
    degree D = 0 ↔ D = 0 := by
  have hD' : WeilDivisor.IsEffective D := WeilDivisor.isEffective_iff_zero_le.mpr hD
  simpa only [degree] using
    hD'.weightedDegree_eq_zero_iff_of_pos (degree_pos_of_isFunctionField hF)

/-- Equality of degrees under a coefficientwise inequality forces equality of divisors. -/
lemma eq_of_le_of_degree_eq (hF : IsFunctionField k F) {D E : Divisor k F} (hDE : D ≤ E)
    (hdeg : degree D = degree E) : D = E := by
  apply WeilDivisor.eq_of_le_of_weightedDegree_eq_of_pos
    (degree_pos_of_isFunctionField hF) hDE
  simpa only [degree] using hdeg

end Divisor

end TauCeti
