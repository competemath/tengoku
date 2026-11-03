import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms algebraMap_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms coefficientMap_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fractionMap_algebraMap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fractionMap_injective` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Generic base localization

For a torsion-free algebra over a domain, invert the images of every nonzero
base element.  The algebra embeds in that localization and the fraction field
of the base maps canonically into it.
-/

noncomputable section
namespace AlbertLean.Generic.GenericBaseLocalization

universe u v
variable (A : Type u) (B : Type v) [CommRing A] [CommRing B]
  [IsDomain A] [Nontrivial B] [Algebra A B] [Module.IsTorsionFree A B]

/-- Images in `B` of the nonzero elements of the domain `A`.-/
def baseNonzeroImages : Submonoid B :=
  (nonZeroDivisors A).map (algebraMap A B)

/-- Base change of `B` from `A` to its fraction field, presented as a
localization of `B`.-/
abbrev GenericBaseRing := Localization (baseNonzeroImages A B)

private theorem baseNonzeroImages_le_nonZeroDivisors :
    baseNonzeroImages A B ≤ nonZeroDivisors B := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_nonZeroDivisors_iff_right]
  intro b hab
  have hs : a • b = 0 := by
    simpa only [Algebra.smul_def, mul_comm] using hab
  exact (smul_eq_zero.mp hs).resolve_left
    (mem_nonZeroDivisors_iff_ne_zero.mp ha)

/-- Torsion-freeness is precisely what prevents a nonzero base denominator
from killing an element of `B`.
@isnad1 id=injectiv.0h2v.s7.e32321056b23 from=translated src=- shape=1783b052 vocab=abb63d2d
-/
theorem algebraMap_injective : Function.Injective
    (algebraMap B (GenericBaseRing A B)) :=
  IsLocalization.injective (GenericBaseRing A B)
    (baseNonzeroImages_le_nonZeroDivisors A B)

/-- The composite coefficient map from `A` into the generic base ring.-/
def coefficientMap : A →+* GenericBaseRing A B :=
  (algebraMap B (GenericBaseRing A B)).comp (algebraMap A B)

/--
@isnad1 id=injectiv.0h2v.s7.64a3c2526db2 from=translated src=- shape=cf62c061 vocab=3e493984
-/
theorem coefficientMap_injective : Function.Injective (coefficientMap A B) :=
  (algebraMap_injective A B).comp
    (FaithfulSMul.algebraMap_injective A B)

/-- Canonical extension of the coefficient map to `Frac(A)`.-/
def fractionMap : FractionRing A →+* GenericBaseRing A B :=
  IsLocalization.lift (M := nonZeroDivisors A) (S := FractionRing A)
    (P := GenericBaseRing A B) (g := coefficientMap A B)
    fun a : nonZeroDivisors A => by
    let b : baseNonzeroImages A B :=
      ⟨algebraMap A B a, ⟨a, a.property, rfl⟩⟩
    change IsUnit (algebraMap B (GenericBaseRing A B) (algebraMap A B a))
    exact IsLocalization.map_units (GenericBaseRing A B) b

/--
@isnad1 id=eq.0h3v.s9.9cee17b5c15b from=translated src=- shape=a8bde244 vocab=09aad4f1
-/
@[simp] theorem fractionMap_algebraMap (a : A) :
    fractionMap A B (algebraMap A (FractionRing A) a) = coefficientMap A B a :=
  by
    unfold fractionMap
    exact IsLocalization.lift_eq _ a

/-- The canonical fraction-field map is injective because its source is a
field and its target is nontrivial.
@isnad1 id=injectiv.0h2v.s7.7bf704c95c90 from=translated src=- shape=8d452bd4 vocab=868ccb8c
-/
theorem fractionMap_injective : Function.Injective (fractionMap A B) :=
  haveI : Nontrivial (GenericBaseRing A B) :=
    (algebraMap_injective A B).nontrivial
  RingHom.injective (fractionMap A B)

end AlbertLean.Generic.GenericBaseLocalization
