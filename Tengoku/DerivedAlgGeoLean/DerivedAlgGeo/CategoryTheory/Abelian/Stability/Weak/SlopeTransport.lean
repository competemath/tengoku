/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeTop
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Functorial
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.SubobjectEquivalence
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transporting weak slope data along an equivalence of abelian categories

`WeakSlopeData A` is two homomorphisms out of `K₀Ab A` together with two sign conditions, so an
equivalence `e : A ≌ B` carries it to `WeakSlopeData B` by precomposing with `K₀Ab.congr e`. This
file does that and records what the transported rank, degree, slope and charge are.

## Why it is needed

Numerical data is written on the category the objects live in. The stability machinery is written
on the heart of a t-structure. `Algebra/Homology/DerivedCategory/Heart.lean` identifies the two for
the canonical t-structure, and this file is what lets a slope defined on the first be read on the
second — the concrete case being the μ-slope of the Gieseker lane, which is defined on coherent
sheaves while the Mukai tilt assembly wants it on a heart.

## The direction to keep straight

`congr` transports *along* `e`, so the transported data on `B` evaluates an object by pulling it
back through `e.inverse`. Both readings are recorded: `congr_rank` is the one that holds by
definition, and `congr_rank_functor` is the one a consumer starting from an object of `A` wants.
Nothing is transported by `rfl` alone — `congr_rank_functor` needs the unit isomorphism, which is
why it is a theorem and not a `simp` unfolding.

## Semistability

Semistability is not a statement about a homomorphism: it quantifies over the subobjects of an
object. It transports because `Subobject.mapEquivalence` is an order isomorphism and in particular
surjective, so every subobject of the image is the image of a subobject, and its slope is the
original slope by `mapFunctorIso`.

## What is not here

The Harder–Narasimhan property itself. A filtration also names the cokernel of each chain step, so
transporting one needs `Subobject.cokernelOfLEMapFunctorIso` and an isomorphism-invariance lemma
for filtrations that does not yet exist.
-/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Triangulated

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- An equivalence reflects nonzero objects: the inverse of a nonzero object is nonzero.
@isnad1 id=not.1h4v.s5.e5f592165f84 from=translated src=- shape=5ab37df2 vocab=9f3f4edf
-/
theorem not_isZero_inverse_obj (e : A ≌ B) {E : B} (hE : ¬IsZero E) :
    ¬IsZero (e.inverse.obj E) := by
  intro hz
  exact hE ((e.functor.map_isZero hz).of_iso (e.counitIso.app E).symm)

namespace WeakSlopeData

variable (D : WeakSlopeData A) (e : A ≌ B)

/-- **Weak slope data transported along an equivalence.**

Both homomorphisms are precomposed with `K₀Ab.congr e` run backwards, so the transported data reads
an object of `B` by pulling it back to `A`. The two sign conditions transport because the pullback
of a nonzero object is nonzero.-/
def congr : WeakSlopeData B where
  rankHom := D.rankHom.comp (K₀Ab.congr e).symm.toAddMonoidHom
  degreeHom := D.degreeHom.comp (K₀Ab.congr e).symm.toAddMonoidHom
  rank_nonneg E := by
    simpa using D.rank_nonneg (e.inverse.obj E)
  degree_nonneg_of_rank_zero E hE hrank := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, K₀Ab.congr_symm_of] at hrank ⊢
    exact D.degree_nonneg_of_rank_zero _ (not_isZero_inverse_obj e hE) hrank

/--
@isnad1 id=eq.0h5v.s6.0fc62eb5a3fd from=translated src=- shape=774fce14 vocab=0419dd76
-/
@[simp]
theorem congr_rank (E : B) : (D.congr e).rank E = D.rank (e.inverse.obj E) := by
  simp [congr, rank]

/--
@isnad1 id=eq.0h5v.s6.7243ec244cb8 from=translated src=- shape=774fce14 vocab=e1a7217e
-/
@[simp]
theorem congr_degree (E : B) : (D.congr e).degree E = D.degree (e.inverse.obj E) := by
  simp [congr, degree]

/-- The reading a consumer starting from an object of `A` wants. It is the unit isomorphism, not
`rfl`. It is deliberately not a `simp` lemma: `congr_rank` already rewrites the left-hand side to
the `e.inverse` form, so both cannot fire.
@isnad1 id=eq.0h5v.s6.31e15f9f5c5f from=translated src=- shape=fd3f22b9 vocab=69772fe9
-/
theorem congr_rank_functor (X : A) : (D.congr e).rank (e.functor.obj X) = D.rank X := by
  rw [congr_rank]
  exact D.rank_iso (e.unitIso.app X).symm

/--
@isnad1 id=eq.0h5v.s6.fad94176cc97 from=translated src=- shape=fd3f22b9 vocab=39ae4c9e
-/
theorem congr_degree_functor (X : A) : (D.congr e).degree (e.functor.obj X) = D.degree X := by
  rw [congr_degree]
  exact D.degree_iso (e.unitIso.app X).symm

/--
@isnad1 id=eq.0h5v.s6.18a46906684b from=translated src=- shape=774fce14 vocab=8334ba22
-/
@[simp]
theorem congr_charge (E : B) : (D.congr e).charge E = D.charge (e.inverse.obj E) := by
  apply Complex.ext <;> simp

/--
@isnad1 id=eq.0h5v.s6.501cc54e9720 from=translated src=- shape=fd3f22b9 vocab=279e359b
-/
theorem congr_charge_functor (X : A) : (D.congr e).charge (e.functor.obj X) = D.charge X := by
  apply Complex.ext
  · simp only [charge_re, congr_degree_functor]
  · simp only [charge_im, congr_rank_functor]

/--
@isnad1 id=eq.0h5v.s6.58d5826df315 from=translated src=- shape=774fce14 vocab=4157b000
-/
@[simp]
theorem congr_slope (E : B) : (D.congr e).slope E = D.slope (e.inverse.obj E) := by
  simp only [slope, congr_rank, congr_degree]

/--
@isnad1 id=eq.0h5v.s6.4fa2c213dcbd from=translated src=- shape=fd3f22b9 vocab=a0df1004
-/
theorem congr_slope_functor (X : A) : (D.congr e).slope (e.functor.obj X) = D.slope X := by
  simp only [slope, congr_rank_functor, congr_degree_functor]

/-- The honest slope transports too. The two cases are rank zero, where both sides are `⊤`, and
positive rank, where both sides are the coerced ratio.
@isnad1 id=eq.0h5v.s6.2f090cd422bf from=translated src=- shape=79e8a32f vocab=b121fc35
-/
@[simp]
theorem congr_topSlope (E : B) : (D.congr e).topSlope E = D.topSlope (e.inverse.obj E) := by
  have hrank : (D.congr e).rank E = D.rank (e.inverse.obj E) := congr_rank D e E
  rcases eq_or_lt_of_le ((D.congr e).rank_nonneg E) with h | h
  · rw [(D.congr e).topSlope_of_rank_zero h.symm,
      D.topSlope_of_rank_zero (by rw [← hrank]; exact h.symm)]
  · rw [(D.congr e).topSlope_of_rank_pos h,
      D.topSlope_of_rank_pos (by rw [← hrank]; exact h), congr_slope]

/--
@isnad1 id=eq.0h5v.s6.d0fccbcbd0f4 from=translated src=- shape=1bdc0ac7 vocab=ca81a3f3
-/
theorem congr_topSlope_functor (X : A) :
    (D.congr e).topSlope (e.functor.obj X) = D.topSlope X := by
  have hrank : (D.congr e).rank (e.functor.obj X) = D.rank X := congr_rank_functor D e X
  rcases eq_or_lt_of_le ((D.congr e).rank_nonneg (e.functor.obj X)) with h | h
  · rw [(D.congr e).topSlope_of_rank_zero h.symm,
      D.topSlope_of_rank_zero (by rw [← hrank]; exact h.symm)]
  · rw [(D.congr e).topSlope_of_rank_pos h,
      D.topSlope_of_rank_pos (by rw [← hrank]; exact h), congr_slope_functor]

/-- An equivalence carries nonzero objects to nonzero objects.
@isnad1 id=not.1h4v.s5.ff39208c69b3 from=translated src=- shape=80dfe002 vocab=ba567088
-/
theorem not_isZero_functor_obj {Z : A} (hZ : ¬IsZero Z) : ¬IsZero (e.functor.obj Z) := by
  intro hz
  exact hZ ((e.inverse.map_isZero hz).of_iso (e.unitIso.app Z))

/-- **The slope of a transported subobject is the original slope.**
@isnad1 id=eq.0h6v.s7.9cbfad98d879 from=translated src=- shape=5bfa48b0 vocab=be004a7b
-/
theorem congr_topSlope_mapFunctor {Z : A} (P : Subobject Z)
    [e.functor.PreservesMonomorphisms] :
    (D.congr e).topSlope
        ((Subobject.mapFunctor e.functor P : Subobject (e.functor.obj Z)) : B) =
      D.topSlope ((P : A)) := by
  rw [show (D.congr e).topSlope
      ((Subobject.mapFunctor e.functor P : Subobject (e.functor.obj Z)) : B) =
      (D.congr e).topSlope (e.functor.obj (P : A)) from
    (D.congr e).toWeakStabilityFunction.slope_eq_of_iso
      (Subobject.mapFunctorIso e.functor P)]
  exact congr_topSlope_functor D e _

/-- **Semistability transports along an equivalence.**

Every subobject of the image is the image of a subobject, because `Subobject.mapEquivalence` is an
order isomorphism and so surjective; its slope is the original slope.
@isnad1 id=issemist.1h5v.s6.5a1909e86586 from=translated src=- shape=3157ab85 vocab=94400f90
-/
theorem congr_isSemistable [e.functor.PreservesMonomorphisms]
    [e.inverse.PreservesMonomorphisms] {Z : A}
    (h : D.toWeakStabilityFunction.IsSemistable Z) :
    (D.congr e).toWeakStabilityFunction.IsSemistable (e.functor.obj Z) := by
  refine ⟨not_isZero_functor_obj e h.1, ?_⟩
  intro P' hP'
  obtain ⟨P, rfl⟩ := (Subobject.mapEquivalence e Z).surjective P'
  rw [Subobject.mapEquivalence_apply] at hP' ⊢
  have hP : ¬IsZero ((P : A)) := by
    intro hz
    exact hP' ((e.functor.map_isZero hz).of_iso
      (Subobject.mapFunctorIso e.functor P))
  have hslope := congr_topSlope_mapFunctor D e P
  have hZ := congr_topSlope_functor D e Z
  show (D.congr e).topSlope _ ≤ (D.congr e).topSlope _
  rw [hslope, hZ]
  exact h.2 P hP

end WeakSlopeData

end CategoryTheory.Triangulated
