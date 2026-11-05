/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.Composition
import Tengoku.AclGeom.AclGeom.Correspondence.BaseChange
import Tengoku.AclGeom.AclGeom.Correspondence.CurveIdeal
import Tengoku.Seed.Algebra.MvPolynomial.Nilpotent
import Tengoku.Seed.RingTheory.MvPolynomial.MonomialOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical equations of finite-correspondence germs

A generic finite correspondence on the affine line has a principal prime
vanishing ideal.  A generator of that ideal is only determined up to a
nonzero scalar, so its coefficients do not yet give intrinsic coordinates
on a family of correspondences.  This file removes that ambiguity by making
the generator monic for the fixed lexicographic monomial order.

The resulting `curveEquation` is determined by the branch ideal itself.
This is the normalization needed before adjoining its coefficients to form
the parameter field of a correspondence germ.
-/

namespace AclGeom

open MvPolynomial
open scoped MonomialOrder

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

namespace FiniteCorrespondencePair

variable (P : FiniteCorrespondencePair k Ω)

/-- The source coordinate of a finite-correspondence pair is transcendental
over the field of definition.-/
theorem source_transcendental' : Transcendental k P.source := by
  intro h
  exact P.source_generic (mem_racl_empty_of_isAlgebraic h)

/-- An arbitrary prime generator of the curve ideal.  Its scalar ambiguity
is removed in `curveEquation` below.-/
private def rawCurveEquation : MvPolynomial (Fin 2) k :=
  Classical.choose
    (exists_prime_span_idealOf k P.source_transcendental' P.target_mem_source)

private theorem rawCurveEquation_prime : Prime P.rawCurveEquation :=
  (Classical.choose_spec
    (exists_prime_span_idealOf k P.source_transcendental' P.target_mem_source)).1

private theorem ideal_eq_span_rawCurveEquation :
    P.ideal = Ideal.span {P.rawCurveEquation} :=
  (Classical.choose_spec
    (exists_prime_span_idealOf k P.source_transcendental' P.target_mem_source)).2

/-- The intrinsic equation of a finite-correspondence branch: the prime
generator of its ideal, scaled to have lexicographic leading coefficient
one.-/
def curveEquation : MvPolynomial (Fin 2) k :=
  C ((MonomialOrder.lex.leadingCoeff P.rawCurveEquation)⁻¹) * P.rawCurveEquation

private theorem leadingCoeff_rawCurveEquation_ne_zero :
    MonomialOrder.lex.leadingCoeff P.rawCurveEquation ≠ 0 :=
  MonomialOrder.leadingCoeff_ne_zero_iff.mpr P.rawCurveEquation_prime.ne_zero

/-- The canonical curve equation is monic in the fixed lexicographic order.-/
theorem curveEquation_monic : MonomialOrder.lex.Monic P.curveEquation := by
  rw [MonomialOrder.Monic, curveEquation, MonomialOrder.leadingCoeff_mul,
    MonomialOrder.leadingCoeff_C]
  exact inv_mul_cancel₀ P.leadingCoeff_rawCurveEquation_ne_zero

private theorem curveEquation_associated_raw :
    Associated P.curveEquation P.rawCurveEquation := by
  apply associated_unit_mul_left
  exact IsUnit.map MvPolynomial.C
    (isUnit_iff_ne_zero.mpr (inv_ne_zero P.leadingCoeff_rawCurveEquation_ne_zero))

/-- The canonical equation generates exactly the branch ideal.-/
theorem ideal_eq_span_curveEquation :
    P.ideal = Ideal.span {P.curveEquation} := by
  rw [P.ideal_eq_span_rawCurveEquation]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    P.curveEquation_associated_raw.symm

/-- Two lexicographically monic equations which generate the same principal
ideal are literally equal.  This public form is useful when a coefficient-
field equivalence transports one canonical curve equation to another.-/
theorem eq_of_monic_of_associated
    {f g : MvPolynomial (Fin 2) k}
    (hf : MonomialOrder.lex.Monic f) (hg : MonomialOrder.lex.Monic g)
    (hfg : Associated f g) : f = g := by
  obtain ⟨u, hu⟩ := hfg
  obtain ⟨c, hcunit, huc⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hlc : MonomialOrder.lex.leadingCoeff (f * (u : MvPolynomial (Fin 2) k)) = c := by
    rw [huc, MonomialOrder.leadingCoeff_mul, MonomialOrder.leadingCoeff_C,
      hf.leadingCoeff_eq_one, one_mul]
  have hc : c = 1 := by
    rw [hu, hg.leadingCoeff_eq_one] at hlc
    exact hlc.symm
  rw [← hu, huc, hc, map_one, mul_one]

section CoefficientField

variable (k : Type*) [Field k] [Algebra k Ω]
variable (E : IntermediateField k Ω)
variable (P : FiniteCorrespondencePair E Ω)

/-- The coefficients of the canonical curve equation, viewed in the common
ambient field.  Taking the range over all monomials is harmless: all but
finitely many entries are zero.-/
def curveCoefficientSet : Set Ω :=
  Set.range fun d : (Fin 2 →₀ ℕ) => ((P.curveEquation.coeff d : E) : Ω)

/-- The field generated over `k` by the intrinsic coefficients of a finite
correspondence germ defined over an intermediate field `E`.-/
def curveCoefficientField : IntermediateField k Ω :=
  IntermediateField.adjoin k (P.curveCoefficientSet k E)

/-- The canonical coefficients, lifted into the intrinsic field that they
generate.-/
def curveCoefficientCoordinates :
    P.curveCoefficientSet k E → P.curveCoefficientField k E :=
  fun z ↦ ⟨z.1, IntermediateField.subset_adjoin k _ z.2⟩

/-- Every canonical coefficient belongs to the coefficient field.-/
theorem coeff_mem_curveCoefficientField (d : Fin 2 →₀ ℕ) :
    ((P.curveEquation.coeff d : E) : Ω) ∈ P.curveCoefficientField k E :=
  IntermediateField.subset_adjoin k _ ⟨d, rfl⟩

/-- The intrinsic coefficient field is contained in every field of
definition used to present the correspondence.-/
theorem curveCoefficientField_le : P.curveCoefficientField k E ≤ E := by
  rw [curveCoefficientField]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro z ⟨d, rfl⟩
  exact (P.curveEquation.coeff d).2

/-- The canonical equation descended to its own coefficient field.-/
def curveEquationOverCoefficientField :
    MvPolynomial (Fin 2) (P.curveCoefficientField k E) :=
  P.curveEquation.support.sum fun d =>
    monomial d
      ⟨((P.curveEquation.coeff d : E) : Ω),
        P.coeff_mem_curveCoefficientField k E d⟩

end CoefficientField

end FiniteCorrespondencePair

end

end AclGeom
