/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Enriques

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Classification of spherical and pseudoprojective objects up to shift

The classification theorems in the two Enriques papers have a common logical
shape.  A finite family of candidates is constructed, distinct candidates are
graded-orthogonal, and every spherical or pseudoprojective object is isomorphic
to a shift of the appropriate candidate.

This file isolates that shape.  It proves the formal consequences of graded
orthogonality and packages the conclusions of arXiv:1912.04332v2 Proposition
4.10 and arXiv:2104.13610v2 Theorem 2.7 as explicit supplied classification
data.  It does not claim the deep geometric hypotheses needed by those papers:
mutations, admissible projection functors, and the Enriques-surface Ext
calculations are not yet constructed in this repository.
-/

universe w v u t

namespace CategoryTheory.SerreFunctor

open CategoryTheory CategoryTheory.Limits

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [HasShift C ℤ]

/-- `E` is isomorphic to some integral shift of `F`.-/
def IsShiftOf (E F : C) : Prop :=
  ∃ p : ℤ, Nonempty (E ≅ F⟦p⟧)

namespace IsShiftOf

omit [Preadditive C] in
/-- Every object is a shift of itself, with shift zero.
@isnad1 id=isshifto.0h2v.s4.450ded2aea72 from=translated src=- shape=c0a48736 vocab=402e5c1d
-/
theorem refl (E : C) : IsShiftOf E E :=
  ⟨0, ⟨((shiftFunctorZero C ℤ).app E).symm⟩⟩

omit [Preadditive C] in
/-- Being isomorphic up to an integral shift is symmetric.
@isnad1 id=isshifto.1h3v.s4.62a21f77f1eb from=translated src=- shape=4ecd1915 vocab=402e5c1d
-/
theorem symm {E F : C} (h : IsShiftOf E F) : IsShiftOf F E := by
  obtain ⟨p, ⟨e⟩⟩ := h
  refine ⟨-p, ⟨((shiftFunctorCompIsoId C p (-p) (by omega)).app F).symm ≪≫ ?_⟩⟩
  exact (shiftFunctor C (-p)).mapIso e.symm

omit [Preadditive C] in
/-- Integral shifts compose, so `IsShiftOf` is transitive.
@isnad1 id=isshifto.2h4v.s5.b61ffd2ae3d1 from=translated src=- shape=96b24d1f vocab=402e5c1d
-/
theorem trans {E F G : C} (hEF : IsShiftOf E F) (hFG : IsShiftOf F G) :
    IsShiftOf E G := by
  obtain ⟨p, ⟨eEF⟩⟩ := hEF
  obtain ⟨q, ⟨eFG⟩⟩ := hFG
  refine ⟨q + p, ⟨eEF ≪≫ (shiftFunctor C p).mapIso eFG ≪≫ ?_⟩⟩
  exact ((shiftFunctorAdd' C q p (q + p) rfl).app G).symm

omit [Preadditive C] in
/-- Replacing the left object by an isomorphic object preserves
`IsShiftOf`.
@isnad1 id=isshifto.1h5v.s5.cb9a4c8d50b8 from=translated src=- shape=dc50b52e vocab=f6d8c7d0
-/
theorem of_iso_left {E E' F : C} (e : E ≅ E') (h : IsShiftOf E' F) :
    IsShiftOf E F := by
  obtain ⟨p, ⟨e'⟩⟩ := h
  exact ⟨p, ⟨e ≪≫ e'⟩⟩

omit [Preadditive C] in
/-- Replacing the right object by an isomorphic object preserves
`IsShiftOf`.
@isnad1 id=isshifto.1h5v.s5.fc42fef1d522 from=translated src=- shape=96b24d1f vocab=f6d8c7d0
-/
theorem of_iso_right {E F F' : C} (h : IsShiftOf E F) (e : F ≅ F') :
    IsShiftOf E F' := by
  obtain ⟨p, ⟨e'⟩⟩ := h
  exact ⟨p, ⟨e' ≪≫ (shiftFunctor C p).mapIso e⟩⟩

end IsShiftOf

/-- All shifted Homs from `E` to `F` vanish.-/
def IsGradedOrthogonal (E F : C) : Prop :=
  ∀ p : ℤ, ∀ f : E ⟶ F⟦p⟧, f = 0

/-- A nonzero object cannot be a shift of an object to which it is graded
orthogonal.
@isnad1 id=not.2h3v.s5.218cead9a135 from=translated src=- shape=0dbb7ce7 vocab=38069205
-/
theorem not_isShiftOf_of_isGradedOrthogonal {E F : C}
    (hE : ¬ IsZero E) (horth : IsGradedOrthogonal E F) :
    ¬ IsShiftOf E F := by
  rintro ⟨p, ⟨e⟩⟩
  apply hE
  rw [IsZero.iff_id_eq_zero, ← e.hom_inv_id]
  rw [horth p e.hom, zero_comp]

/-- A family of spherical candidates with the completeness and separation
conclusions of Paper I, Proposition 4.10.  The fields are supplied because the
mutation argument proving them is not generic category theory.-/
structure SphericalClassificationData (D : SerreFunctorData k C) (n : ℕ)
    (ι : Type t) where
  /-- The classified candidate family.-/
  candidate : ι → C
  /-- Every candidate is spherical.-/
  candidate_spherical : ∀ i, IsSphericalObject D n (candidate i)
  /-- Distinct candidates are graded-orthogonal.-/
  pairwise_orthogonal : ∀ {i j}, i ≠ j → IsGradedOrthogonal (candidate i) (candidate j)
  /-- Every spherical object is, and only is, a shift of a candidate.-/
  complete : ∀ E : C, IsSphericalObject D n E ↔ ∃ i, IsShiftOf E (candidate i)

namespace SphericalClassificationData

variable {D : SerreFunctorData k C} {n : ℕ} {ι : Type t}
  (A : SphericalClassificationData D n ι)

/-- Distinct candidates are not isomorphic up to any shift.
@isnad1 id=not.1h8v.s6.f7854b3ba614 from=translated src=- shape=7da670ba vocab=d0cd260f
-/
theorem candidate_not_isShiftOf {i j : ι} (hij : i ≠ j) :
    ¬ IsShiftOf (A.candidate i) (A.candidate j) :=
  not_isShiftOf_of_isGradedOrthogonal
    (A.candidate_spherical i).not_isZero (A.pairwise_orthogonal hij)

/-- Find a candidate and shift representing a spherical object.
@isnad1 id=ex.1h7v.s6.39ccf38e9300 from=translated src=- shape=665c2d86 vocab=6369827f
-/
theorem exists_candidate_shift {E : C} (hE : IsSphericalObject D n E) :
    ∃ (i : ι) (p : ℤ), Nonempty (E ≅ (A.candidate i)⟦p⟧) := by
  obtain ⟨i, p, e⟩ := (A.complete E).mp hE
  exact ⟨i, p, e⟩

end SphericalClassificationData

/-- The mixed classification pattern of Paper II, Theorem 2.7.

`blockLength i = 1` marks the spherical candidates and `2 ≤ blockLength i`
marks the pseudoprojective candidates.  The intended paper specialization is
`n = 3`.-/
structure MixedClassificationData (D : SerreFunctorData k C) (n : ℕ)
    (ι : Type t) where
  /-- The length of the exceptional block producing a candidate.-/
  blockLength : ι → ℕ
  /-- The projected candidate object.-/
  candidate : ι → C
  /-- Length-one blocks produce spherical candidates.-/
  spherical_of_length_one : ∀ i, blockLength i = 1 →
    IsSphericalObject D n (candidate i)
  /-- Longer blocks produce pseudoprojective candidates.-/
  pseudoprojective_of_two_le : ∀ i, 2 ≤ blockLength i →
    IsPseudoprojectiveObject D n (candidate i)
  /-- Distinct candidates are graded-orthogonal.-/
  pairwise_orthogonal : ∀ {i j}, i ≠ j → IsGradedOrthogonal (candidate i) (candidate j)
  /-- Classification of all spherical objects.-/
  spherical_complete : ∀ E : C, IsSphericalObject D n E ↔
    ∃ i, blockLength i = 1 ∧ IsShiftOf E (candidate i)
  /-- Classification of all pseudoprojective objects.-/
  pseudoprojective_complete : ∀ E : C, IsPseudoprojectiveObject D n E ↔
    ∃ i, 2 ≤ blockLength i ∧ IsShiftOf E (candidate i)

namespace MixedClassificationData

variable {D : SerreFunctorData k C} {n : ℕ} {ι : Type t}
  (A : MixedClassificationData D n ι)

/-- A length-one candidate is spherical.
@isnad1 id=isspheri.1h7v.s6.34fc9ee3c80c from=translated src=- shape=ad25d2f4 vocab=7ca32768
-/
theorem candidate_spherical {i : ι} (hi : A.blockLength i = 1) :
    IsSphericalObject D n (A.candidate i) :=
  A.spherical_of_length_one i hi

/-- A longer-block candidate is pseudoprojective.
@isnad1 id=ispseudo.1h7v.s6.756c89074213 from=translated src=- shape=b92094b0 vocab=ba5063bb
-/
theorem candidate_pseudoprojective {i : ι} (hi : 2 ≤ A.blockLength i) :
    IsPseudoprojectiveObject D n (A.candidate i) :=
  A.pseudoprojective_of_two_le i hi

/-- Distinct spherical candidates are not isomorphic up to shift.
@isnad1 id=not.2h8v.s6.44fa398af901 from=translated src=- shape=a9cc9822 vocab=56e3cf5e
-/
theorem spherical_candidate_not_isShiftOf {i j : ι}
    (hi : A.blockLength i = 1) (hij : i ≠ j) :
    ¬ IsShiftOf (A.candidate i) (A.candidate j) :=
  not_isShiftOf_of_isGradedOrthogonal
    (A.candidate_spherical hi).not_isZero (A.pairwise_orthogonal hij)

/-- Distinct pseudoprojective candidates are not isomorphic up to shift.
@isnad1 id=not.2h8v.s6.42952f768db5 from=translated src=- shape=5ac8917b vocab=e406d832
-/
theorem pseudoprojective_candidate_not_isShiftOf {i j : ι}
    (hi : 2 ≤ A.blockLength i) (hij : i ≠ j) :
    ¬ IsShiftOf (A.candidate i) (A.candidate j) :=
  not_isShiftOf_of_isGradedOrthogonal
    (A.candidate_pseudoprojective hi).not_isZero (A.pairwise_orthogonal hij)

/-- Exact spherical half of the Paper II classification.
@isnad1 id=iff.0h7v.s6.17e2c3926f0b from=translated src=- shape=46a1f568 vocab=5f006a4b
-/
theorem spherical_iff (E : C) : IsSphericalObject D n E ↔
    ∃ i, A.blockLength i = 1 ∧ IsShiftOf E (A.candidate i) :=
  A.spherical_complete E

/-- Exact pseudoprojective half of the Paper II classification.
@isnad1 id=iff.0h7v.s6.4b672762fc5b from=translated src=- shape=12e62a97 vocab=93f8db25
-/
theorem pseudoprojective_iff (E : C) : IsPseudoprojectiveObject D n E ↔
    ∃ i, 2 ≤ A.blockLength i ∧ IsShiftOf E (A.candidate i) :=
  A.pseudoprojective_complete E

end MixedClassificationData

end CategoryTheory.SerreFunctor
