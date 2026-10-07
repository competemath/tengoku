/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Kraenzle, Judith Ludwig, Bryan Wang, Christian Merten,
  Yannis Monbru, Alireza Shavali, Chenyi Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Properties
public import Tengoku.Seed.AlgebraicGeometry.Fiber

/-!
# Geometrically-`P` schemes over a field

In this file we define the basic interface for properties like geometrically reduced,
geometrically irreducible, geometrically connected etc. In this file
we treat an abstract property of schemes `P` and derive the general properties that are
shared by all of these variants.

A morphism of schemes `f : X ⟶ Y` is geometrically `P` if for any field `K` and
morphism `Spec K ⟶ Y`, the base change `X ×[Y] Spec K` satisfies `P`.

## Main definitions and results

- `AlgebraicGeometry.geometrically`: The morphism property of geometrically-`P` morphisms
- `AlgebraicGeometry.geometrically_iff_forall_fiberToSpecResidueField`: `f : X ⟶ Y` is
  geometrically-`P` if and only if for every `y : Y`, the fiber `f ⁻¹ {y}` is geometrically-`P`
  over `Spec κ(y)`.

## Notes

This contribution was created as part of the Formalising Algebraic Geometry workshop 2025 in
Heidelberg.
-/

@[expose] public section

universe u

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is geometrically `P` if for any field `K` and
morphism `Spec K ⟶ Y`, the base change `X ×[Y] Spec K` satisfies `P`. -/
def geometrically (P : ObjectProperty Scheme.{u}) : MorphismProperty Scheme.{u} :=
  fun X Y f ↦ ∀ ⦃K : Type u⦄ [Field K] (y : Spec (.of K) ⟶ Y)
    ⦃Z : Scheme.{u}⦄ (fst : Z ⟶ X) (snd : Z ⟶ Spec (.of K)),
    IsPullback fst snd f y → P Z

/--
@isnad1 id=eq.0h1v.s5.fee9fe066106 from=seed src=0 shape=7f3d55c7 vocab=8f7b5044
-/
lemma geometrically_eq_universally (P : ObjectProperty Scheme.{u}) :
    geometrically P = .universally fun X Y _ ↦ IsIntegral Y → Subsingleton Y → P X := by
  ext X Y f
  refine ⟨fun hf Z W snd q fst h _ _ ↦ ?_, fun hf aK y Z W fst snd h ↦ ?_⟩
  · let := (isField_of_isIntegral_of_subsingleton W).toField
    apply hf (W.isoSpec.inv ≫ q) snd (fst ≫ W.isoSpec.hom)
    apply h.flip.of_iso (.refl _) (.refl _) W.isoSpec (.refl _) <;> simp
  · exact hf _ _ _ h.flip inferInstance inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s6.5138e955241f from=seed src=0 shape=f8108c88 vocab=4449d6ed
-/
lemma geometrically_inf (P Q : ObjectProperty Scheme.{u}) :
    geometrically (P ⊓ Q) = geometrically P ⊓ geometrically Q := by
  simp only [geometrically_eq_universally, ← MorphismProperty.universally_inf]
  congr with X Y f
  exact ⟨fun H ↦ ⟨(H · · |>.1), (H · · |>.2)⟩, fun H a b ↦ ⟨H.1 a b, H.2 a b⟩⟩

variable (P : ObjectProperty Scheme.{u})

set_option backward.isDefEq.respectTransparency.types false in
instance : (geometrically P).IsStableUnderBaseChange := by
  rw [geometrically_eq_universally]
  infer_instance

instance [P.IsClosedUnderIsomorphisms] : IsZariskiLocalAtTarget (geometrically P) := by
  rw [geometrically_eq_universally]
  refine universally_isZariskiLocalAtTarget _ fun {X} Y f ι U hU H _ _ ↦ ?_
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨i, hy⟩ := hU.exists_mem y
  have heq : U i = ⊤ := eq_top_iff.mpr fun z _ ↦ by rwa [Subsingleton.elim z y]
  let e : ↑(U i) ≅ Y := Y.isoOfEq heq ≪≫ Y.topIso
  let e' : ↑(f ⁻¹ᵁ U i) ≅ X := X.isoOfEq (by simp [heq]) ≪≫ X.topIso
  exact P.prop_of_iso e' <| H i (.of_isIso e.inv) (e.hom.homeomorph.subsingleton_congr.mpr ‹_›)

section geometrically

variable {P : ObjectProperty Scheme.{u}} {X Y : Scheme.{u}} {f : X ⟶ Y}

/--
@isnad1 id=var.0h7v.s5.f3b185fdacc4 from=seed src=0 shape=178fe550 vocab=8457f0dc
-/
lemma pullback_of_geometrically (hf : geometrically P f) (K : Type u) [Field K]
    (y : Spec (.of K) ⟶ Y) : P (Limits.pullback f y) :=
  hf _ _ _ (.of_hasPullback _ _)

/--
@isnad1 id=var.0h7v.s5.afb69a28099e from=seed src=0 shape=d2a12931 vocab=8457f0dc
-/
lemma pullback_of_geometrically' (hf : geometrically P f) (K : Type u) [Field K]
    (y : Spec (.of K) ⟶ Y) : P (Limits.pullback y f) :=
  hf _ _ _ (.flip <| .of_hasPullback _ _)

/--
@isnad1 id=iff.0h4v.s6.e8ae0198c4f4 from=seed src=0 shape=9349eba0 vocab=0ab469dc
-/
lemma geometrically_iff_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    geometrically P f ↔
      ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ Y), P (Limits.pullback f y) := by
  refine ⟨fun h K _ _ ↦ pullback_of_geometrically h _ _, fun H K _ _ Y fst snd h ↦ ?_⟩
  exact P.prop_of_iso h.isoPullback.symm (H _ _)

/--
@isnad1 id=var.0h6v.s5.2d2136c737fd from=seed src=0 shape=c2eddf72 vocab=475ef688
-/
lemma fiber_of_geometrically (hf : geometrically P f) (y : Y) : P (f.fiber y) :=
  pullback_of_geometrically hf _ _

set_option backward.isDefEq.respectTransparency false in
/-- `P` holds geometrically for `f` if and only if all fibers are geometrically `P`.
@isnad1 id=iff.0h4v.s5.d6437f6be588 from=seed src=0 shape=57e0a23b vocab=28133200
-/
lemma geometrically_iff_forall_fiberToSpecResidueField :
    geometrically P f ↔ ∀ (y : Y), geometrically P (f.fiberToSpecResidueField y) := by
  refine ⟨fun hf y ↦ (geometrically P).pullback_snd _ _ hf, fun H ↦ ?_⟩
  intro K _ y Z fst snd h
  obtain ⟨⟨y, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField _ _).symm.surjective y
  let p : Z ⟶ f.fiber y :=
    pullback.lift fst (snd ≫ Spec.map φ) (by simp [h.w, Scheme.SpecToEquivOfField])
  apply H y (Spec.map φ) p snd
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at h
  refine .flip (.of_bot (.flip ?_) ?_ (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip)
  · convert! h
    simp [p]
  · simp [p, Scheme.Hom.fiberToSpecResidueField]

/-- This holds in particular if `Y = Spec K`.
@isnad1 id=var.0h5v.s5.727f9191e89b from=seed src=0 shape=082c2523 vocab=1d59ea27
-/
lemma self_of_isIntegral_of_geometrically [IsIntegral Y] [Subsingleton Y] (hf : geometrically P f) :
    P X := by
  rw [geometrically_eq_universally] at hf
  exact MorphismProperty.universally_le _ _ hf ‹_› ‹_›

variable {P : ObjectProperty Scheme.{u}} {R : Type u} [CommRing R] {f : X ⟶ Spec (.of R)}

/--
@isnad1 id=iff.0h4v.s7.6f3a4209a0c1 from=seed src=0 shape=36cb3592 vocab=cfe263f1
-/
lemma geometrically_iff_of_commRing :
    geometrically P f ↔ ∀ ⦃K : Type u⦄ [Field K] [Algebra R K] ⦃Y : Scheme.{u}⦄ (fst : Y ⟶ X)
      (snd : Y ⟶ Spec (.of K)), IsPullback fst snd f (Spec.map <| ofHom (algebraMap R K)) →
      P Y := by
  refine ⟨fun hs K _ _ Z fst snd h ↦ hs _ _ _ h, fun H K _ y Z fst snd h ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  exact H fst snd h

/--
@isnad1 id=iff.0h4v.s6.744c09c72a5e from=seed src=0 shape=c974e18b vocab=d4c3dd58
-/
lemma geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    geometrically P f ↔ ∀ (K : Type u) [Field K] [Algebra R K],
      P (Limits.pullback f (Spec.map <| ofHom <| algebraMap R K)) := by
  refine ⟨fun hf K _ _ ↦ pullback_of_geometrically hf _ _, fun H ↦ ?_⟩
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  exact H K

end geometrically

end AlgebraicGeometry
