/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar, Jireh Loreaux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!

# Projections in C⋆-algebras

Here we collect results about projections specific to C⋆-algebras.

## Main results

+ `isStarProjection_iff_isIdempotentElem_and_isStarNormal`: star projections are precisely
  idempotent normal elements.
+ `IsStarProjection.le_tfae`: for star projections `p` and `q`, the following are equivalent:
  - `p ≤ q`
  - `q * p = p`
  - `p * q = p`
  - `q - p` is a star projection
  - `q - p` is an idempotent element

-/

public section

open scoped CStarAlgebra

section NonUnital
variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A]

/--
@isnad1 id=iff.0h2v.s8.b7b2577f8c18 from=seed src=0 shape=a69d910a vocab=a77b5d36
-/
lemma isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {p : A} :
    IsStarProjection p ↔ quasispectrum ℝ p ⊆ {0, 1} ∧ IsSelfAdjoint p :=
  (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_quasispectrum_subset ℝ p h

section Normal
variable [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- An idempotent element in a non-unital C⋆-algebra is self-adjoint iff it is normal.
@isnad1 id=iff.1h2v.s8.5ca48cebc1be from=seed src=0 shape=677e9f6b vocab=b1d4aaf0
-/
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal {p : A} (hp : IsIdempotentElem p) :
    IsSelfAdjoint p ↔ IsStarNormal p := by
  simp only [isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts,
    QuasispectrumRestricts.real_iff, and_iff_left_iff_imp]
  intro h x hx
  rcases hp.quasispectrum_subset _ hx with (hx | hx) <;> simp [Set.mem_singleton_iff.mp hx]

/-- An element in a non-unital C⋆-algebra is a star projection
if and only if it is idempotent and normal.
@isnad1 id=iff.0h2v.s8.599b7ffbf561 from=seed src=0 shape=faf1c113 vocab=4b9fcadd
-/
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal {p : A} :
    IsStarProjection p ↔ IsIdempotentElem p ∧ IsStarNormal p :=
  (isStarProjection_iff p).eq ▸ and_congr_right_iff.eq ▸ fun h => h.isSelfAdjoint_iff_isStarNormal

/--
@isnad1 id=iff.0h2v.s8.762a269ba53d from=seed src=0 shape=a69d910a vocab=ba9a57f6
-/
theorem isStarProjection_iff_quasispectrum_subset_and_isStarNormal {p : A} :
    IsStarProjection p ↔ quasispectrum ℂ p ⊆ {0, 1} ∧ IsStarNormal p :=
  isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_quasispectrum_subset ℂ p h

end Normal
end NonUnital

section Unital
variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]

/--
@isnad1 id=iff.0h2v.s7.675af28efe6d from=seed src=0 shape=de9e2354 vocab=234e1335
-/
lemma isStarProjection_iff_spectrum_subset_and_isSelfAdjoint [Algebra ℝ A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {p : A} :
    IsStarProjection p ↔ spectrum ℝ p ⊆ {0, 1} ∧ IsSelfAdjoint p :=
  (isStarProjection_iff p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_spectrum_subset ℝ p h

/--
@isnad1 id=iff.0h2v.s7.92c79868f403 from=seed src=0 shape=de9e2354 vocab=9d604309
-/
theorem isStarProjection_iff_spectrum_subset_and_isStarNormal [Algebra ℂ A]
    [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal] {p : A} :
    IsStarProjection p ↔ spectrum ℂ p ⊆ {0, 1} ∧ IsStarNormal p :=
  isStarProjection_iff_isIdempotentElem_and_isStarNormal (p := p).eq ▸
    and_congr_left_iff.mpr fun h ↦ isIdempotentElem_iff_spectrum_subset ℂ p h

end Unital

namespace IsStarProjection

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {p q : A}

open CFC in
/--
@isnad1 id=tfae.2h3v.s8.e73fe569c8dc from=seed src=0 shape=2f6236aa vocab=f7e182b0
-/
lemma le_tfae (hp : IsStarProjection p) (hq : IsStarProjection q) :
  List.TFAE
    [p ≤ q,
    q * p = p,
    p * q = p,
    IsStarProjection (q - p),
    IsIdempotentElem (q - p)] := by
  tfae_have 1 → 2 := fun h ↦ (hq.mul_right_and_mul_left_of_nonneg_of_le hp.nonneg h).2
  tfae_have 2 → 3 := fun h ↦ by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 3 → 4 := hp.sub_of_mul_eq_left hq
  tfae_have 4 → 1 := fun h ↦ by simpa using h.nonneg
  tfae_have 4 ↔ 5 := by simp [isStarProjection_iff, hq.isSelfAdjoint.sub hp.isSelfAdjoint]
  tfae_finish

/--
@isnad1 id=iff.2h3v.s7.93a75838701a from=seed src=0 shape=22158b86 vocab=6bb8f302
-/
lemma le_iff_mul_eq_right (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ q * p = p :=
  hp.le_tfae hq |>.out 1 2

/--
@isnad1 id=iff.2h3v.s7.978383e999c1 from=seed src=0 shape=a0554711 vocab=6bb8f302
-/
lemma le_iff_mul_eq_left (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p * q = p :=
  hp.le_tfae hq |>.out 1 3

/--
@isnad1 id=iff.2h3v.s7.021012749f82 from=seed src=0 shape=b298d08b vocab=197c044d
-/
lemma le_iff_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ IsStarProjection (q - p) :=
  hp.le_tfae hq |>.out 1 4

/--
@isnad1 id=iff.2h3v.s7.77e91fe67ded from=seed src=0 shape=dbe4ef0a vocab=52588d03
-/
lemma le_iff_idempotent_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ IsIdempotentElem (q - p) :=
  hp.le_tfae hq |>.out 1 5

/--
@isnad1 id=commute.3h3v.s7.164741da49f2 from=seed src=0 shape=805d8099 vocab=cb4c4486
-/
lemma commute_of_le (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p ≤ q) :
    Commute p q := by
  rw [commute_iff_eq, hp.le_iff_mul_eq_right hq |>.mp h, hp.le_iff_mul_eq_left hq |>.mp h]

end IsStarProjection
