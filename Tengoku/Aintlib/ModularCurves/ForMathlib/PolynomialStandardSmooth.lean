/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.RingTheory.Smooth.StandardSmooth
import Tengoku.Seed.Algebra.MvPolynomial.Equiv
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial algebras are standard smooth of their rank

The free presentation of `MvPolynomial ι R` (generators `ι`, no relations) is a
submersive presentation of dimension `Nat.card ι`; hence `MvPolynomial ι R` is
standard smooth of relative dimension `Nat.card ι` over `R`, and `Polynomial R`
is standard smooth of relative dimension `1`.

These are the missing base instances for the λ-line chart computation of the
`Y(ρ̄)` smoothness leaf (T-YR-6 (b1)); `IsStandardSmoothOfRelativeDimension`'s
`.trans` and `.localization_away` then give relative dimension 1 for localized
polynomial algebras.
-/

namespace Algebra

open MvPolynomial

variable (R : Type*) [CommRing R] (ι : Type) [Finite ι]

/-- The free submersive presentation of the polynomial algebra: `ι` generators,
no relations, trivially invertible (empty) Jacobian.-/
noncomputable def SubmersivePresentation.mvPolynomialFree :
    SubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{1} where
  toGenerators := Generators.mvPolynomial R ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty, Generators.ker_mvPolynomial]
  map := PEmpty.elim
  map_inj := fun a => a.elim
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian,
      LinearMap.det_eq_one_of_subsingleton, map_one]
    exact isUnit_one

/--
@isnad1 id=eq.0h2v.s7.42769c588681 from=translated src=- shape=867a38b0 vocab=9045a6ff
-/
@[simp]
lemma SubmersivePresentation.mvPolynomialFree_dimension :
    (SubmersivePresentation.mvPolynomialFree R ι).dimension = Nat.card ι := by
  simp [Presentation.dimension]

/-- The polynomial algebra on a finite type is standard smooth of relative
dimension its cardinality.
@isnad1 id=isstanda.0h2v.s6.712612b1f281 from=translated src=- shape=a00266bf vocab=03071e93
-/
theorem IsStandardSmoothOfRelativeDimension.mvPolynomial :
    IsStandardSmoothOfRelativeDimension (Nat.card ι) R (MvPolynomial ι R) :=
  (SubmersivePresentation.mvPolynomialFree R ι).isStandardSmoothOfRelativeDimension
    (SubmersivePresentation.mvPolynomialFree_dimension R ι)

/-- A localization of the one-variable polynomial algebra away from an element
is standard smooth of relative dimension one over the base (the λ-line chart
shape: `R[λ][1/p(λ)]`).
@isnad1 id=isstanda.0h2v.s9.9768b8309287 from=translated src=- shape=f3cac007 vocab=82cebd8b
-/
theorem IsStandardSmoothOfRelativeDimension.localizationAway_mvPolynomialFinOne
    (p : MvPolynomial (Fin 1) R) :
    IsStandardSmoothOfRelativeDimension 1 R (Localization.Away p) := by
  haveI h1 : IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial (Fin 1) R) := by
    have h0 := IsStandardSmoothOfRelativeDimension.mvPolynomial R (Fin 1)
    simpa using h0
  haveI h2 : IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 1) R)
      (Localization.Away p) :=
    IsStandardSmoothOfRelativeDimension.localization_away p
  have h3 := IsStandardSmoothOfRelativeDimension.trans
    (n := 1) (m := 0) (R := R) (S := MvPolynomial (Fin 1) R)
    (T := Localization.Away p)
  simpa using h3

end Algebra

namespace AlgebraicGeometry

open Algebra

universe u

/-- **[T-YR-6 (b2a)]** The `Spec` of a standard-smooth algebra map is smooth of
the same relative dimension.
@isnad1 id=smoothof.0h3v.s6.44e256368bc1 from=translated src=- shape=ab4ceea7 vocab=81d65d2e
-/
theorem smoothOfRelativeDimension_spec_map_algebraMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  exact RingHom.locally_of
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
    (algebraMap R S)
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mpr
      ‹Algebra.IsStandardSmoothOfRelativeDimension n R S›)

end AlgebraicGeometry
