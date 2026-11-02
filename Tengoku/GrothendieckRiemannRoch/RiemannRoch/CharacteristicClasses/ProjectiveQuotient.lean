/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quotient gradings for projective closed subschemes

This file constructs the grading on the quotient of a graded commutative algebra by a
homogeneous ideal.  The homogeneous piece in degree `i` is the image of the original degree-`i`
piece under the quotient map.  It also packages the quotient map as a graded ring homomorphism
and proves the irrelevant-ideal comparison required by `Proj.map`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DirectSum HomogeneousLocalization

universe u

namespace GradedIdealQuotient

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

/-- The degree-`i` piece of a quotient by a homogeneous ideal is the image of the original
degree-`i` piece under the quotient map.-/
def grading (I : HomogeneousIdeal 𝒜) (i : ι) : Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

/-- The quotient map on a homogeneous piece, with codomain restricted to the corresponding
quotient homogeneous piece.-/
def componentMap (I : HomogeneousIdeal 𝒜) (i : ι) :
    𝒜 i →ₗ[R] grading 𝒜 I i where
  toFun x := ⟨Ideal.Quotient.mk I.toIdeal x, ⟨x, x.2, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (Ideal.Quotient.mk I.toIdeal) x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap.map_smul r x.1

/-- Decompose in the original graded algebra and map every component to the quotient.-/
def decomposeToQuotient (I : HomogeneousIdeal 𝒜) :
    A →ₗ[R] ⨁ i, grading 𝒜 I i :=
  (DirectSum.lmap (componentMap 𝒜 I)).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

theorem decomposeToQuotient_eq_zero_of_mem (I : HomogeneousIdeal 𝒜) {x : A}
    (hx : x ∈ I.toIdeal) : decomposeToQuotient 𝒜 I x = 0 := by
  apply DirectSum.ext
  intro i
  apply Subtype.ext
  simp only [decomposeToQuotient, LinearMap.comp_apply,
    DirectSum.lmap_apply, componentMap]
  change Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 x i : A) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (I.isHomogeneous.mem_iff.mp hx) i

/-- The quotient decomposition, obtained by descending the original decomposition through the
homogeneous ideal.-/
def decompose (I : HomogeneousIdeal 𝒜) :
    (A ⧸ I.toIdeal) →ₗ[R] ⨁ i, grading 𝒜 I i where
  toFun := QuotientAddGroup.lift I.toIdeal.toAddSubgroup
    (decomposeToQuotient 𝒜 I).toAddMonoidHom
    (fun x hx ↦ decomposeToQuotient_eq_zero_of_mem 𝒜 I hx)
  map_add' := map_add _
  map_smul' r := by
    rintro ⟨x⟩
    exact (decomposeToQuotient 𝒜 I).map_smul r x

theorem decompose_mk (I : HomogeneousIdeal 𝒜) (x : A) :
    decompose 𝒜 I (Ideal.Quotient.mk I.toIdeal x) = decomposeToQuotient 𝒜 I x :=
  rfl

theorem decompose_coeLinearMap (I : HomogeneousIdeal 𝒜) :
    (decompose 𝒜 I).comp (DirectSum.coeLinearMap (grading 𝒜 I)) = LinearMap.id := by
  ext i x : 2
  obtain ⟨a, ha, hax⟩ := x.2
  have hx : x = componentMap 𝒜 I i ⟨a, ha⟩ := by
    apply Subtype.ext
    exact hax.symm
  subst x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
  change decompose 𝒜 I (Ideal.Quotient.mk I.toIdeal a) =
    DirectSum.lof R ι (fun i ↦ grading 𝒜 I i) i (componentMap 𝒜 I i ⟨a, ha⟩)
  rw [decompose_mk]
  rw [decomposeToQuotient, LinearMap.comp_apply]
  change DirectSum.lmap (componentMap 𝒜 I)
      (DirectSum.decomposeLinearEquiv 𝒜 (⟨a, ha⟩ : 𝒜 i)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.lmap_lof]

theorem coeLinearMap_decompose (I : HomogeneousIdeal 𝒜) :
    (DirectSum.coeLinearMap (grading 𝒜 I)).comp (decompose 𝒜 I) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change DirectSum.coeLinearMap (grading 𝒜 I) (decomposeToQuotient 𝒜 I x) = _
      rw [decomposeToQuotient]
      rw [← LinearMap.comp_apply]
      rw [← LinearMap.comp_assoc]
      rw [show DirectSum.coeLinearMap (grading 𝒜 I) ∘ₗ DirectSum.lmap (componentMap 𝒜 I) =
          (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap ∘ₗ DirectSum.coeLinearMap 𝒜 by
        ext i y : 2
        rfl]
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      change Ideal.Quotient.mk I.toIdeal
          ((DirectSum.decomposeLinearEquiv 𝒜).symm
            ((DirectSum.decomposeLinearEquiv 𝒜) x)) =
        Ideal.Quotient.mk I.toIdeal x
      rw [LinearEquiv.symm_apply_apply]

/-- The quotient homogeneous pieces form an internal direct sum.-/
theorem isInternal (I : HomogeneousIdeal 𝒜) : DirectSum.IsInternal (grading 𝒜 I) := by
  rw [DirectSum.IsInternal]
  change Function.Bijective (DirectSum.coeLinearMap (grading 𝒜 I))
  exact ⟨
    (show Function.LeftInverse (decompose 𝒜 I)
        (DirectSum.coeLinearMap (grading 𝒜 I)) from fun x ↦
      LinearMap.congr_fun (decompose_coeLinearMap 𝒜 I) x).injective,
    (show Function.RightInverse (decompose 𝒜 I)
        (DirectSum.coeLinearMap (grading 𝒜 I)) from fun x ↦
      LinearMap.congr_fun (coeLinearMap_decompose 𝒜 I) x).surjective⟩

/-- Multiplication and the unit respect the quotient homogeneous pieces.-/
instance gradedMonoid (I : HomogeneousIdeal 𝒜) :
    SetLike.GradedMonoid (grading 𝒜 I) where
  one_mem := by
    refine ⟨1, SetLike.one_mem_graded 𝒜, ?_⟩
    exact map_one (Ideal.Quotient.mk I.toIdeal)
  mul_mem i j x y hx hy := by
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    refine ⟨a * b, SetLike.mul_mem_graded ha hb, ?_⟩
    exact map_mul (Ideal.Quotient.mk I.toIdeal) a b

/-- A homogeneous ideal endows its ring quotient with the grading by images of the original
homogeneous pieces.-/
noncomputable instance gradedAlgebra (I : HomogeneousIdeal 𝒜) :
    GradedAlgebra (grading 𝒜 I) :=
  DirectSum.IsInternal.gradedAlgebra (isInternal 𝒜 I)

/-- The quotient map is a graded ring homomorphism for the image grading.-/
def quotientMap (I : HomogeneousIdeal 𝒜) : 𝒜 →+*ᵍ grading 𝒜 I where
  toRingHom := Ideal.Quotient.mk I.toIdeal
  map_mem hx := ⟨_, hx, rfl⟩

@[simp]
theorem quotientMap_apply (I : HomogeneousIdeal 𝒜) (x : A) :
    quotientMap 𝒜 I x = Ideal.Quotient.mk I.toIdeal x :=
  rfl

theorem quotientMap_surjective (I : HomogeneousIdeal 𝒜) :
    Function.Surjective (quotientMap 𝒜 I) :=
  Ideal.Quotient.mk_surjective

/-- Homogeneous localization preserves surjectivity of the quotient map.-/
theorem awayMap_surjective (I : HomogeneousIdeal 𝒜) {d : ι} (s : A) (hs : s ∈ 𝒜 d) :
    Function.Surjective (HomogeneousLocalization.Away.map (quotientMap 𝒜 I) s) := by
  intro z
  obtain ⟨m, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading 𝒜 I) ((quotientMap 𝒜 I).map_mem hs) z
  obtain ⟨a, ha, hax⟩ := hx
  subst x
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 hs m a ha, ?_⟩
  rw [HomogeneousLocalization.Away.map_mk]
  rfl

section Nat

variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The irrelevant ideal of the quotient is contained in the image of the original irrelevant
ideal.  This is precisely the positivity hypothesis required by `Proj.map`.-/
theorem irrelevant_le_map (I : HomogeneousIdeal 𝒜) :
    HomogeneousIdeal.irrelevant (grading 𝒜 I) ≤
      (HomogeneousIdeal.irrelevant 𝒜).map (quotientMap 𝒜 I) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi
  rintro x ⟨a, ha, rfl⟩
  exact Ideal.mem_map_of_mem (quotientMap 𝒜 I)
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi ha)

/-- The projective morphism induced by quotienting a graded ring by a homogeneous ideal.-/
noncomputable def projMap (I : HomogeneousIdeal 𝒜) :
    Proj (grading 𝒜 I) ⟶ Proj 𝒜 :=
  Proj.map (quotientMap 𝒜 I) (irrelevant_le_map 𝒜 I)

/-- On a homogeneous basic open, the quotient `Proj` morphism is the spectrum map induced by
the corresponding homogeneous-localization map.-/
theorem isPullback_away (I : HomogeneousIdeal 𝒜) {d : ℕ} (s : A) (hs : s ∈ 𝒜 d)
    (hd : 0 < d) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (quotientMap 𝒜 I) s)))
      (Proj.awayι (grading 𝒜 I) (quotientMap 𝒜 I s)
        ((quotientMap 𝒜 I).map_mem hs) hd)
      (Proj.awayι 𝒜 s hs hd)
      (projMap 𝒜 I) := by
  apply IsOpenImmersion.isPullback
  · exact Proj.awayι_comp_map (quotientMap 𝒜 I) (irrelevant_le_map 𝒜 I) hd s hs
  · simpa only [Proj.opensRange_awayι, projMap] using
      (Proj.map_preimage_basicOpen (quotientMap 𝒜 I) (irrelevant_le_map 𝒜 I) s)

/-- The `Proj` morphism induced by quotienting by a homogeneous ideal is a closed immersion.-/
theorem isClosedImmersion_projMap (I : HomogeneousIdeal 𝒜) :
    IsClosedImmersion (projMap 𝒜 I) := by
  let 𝒰 := Proj.affineOpenCover 𝒜
  apply IsZariskiLocalAtTarget.of_openCover (𝒰 := 𝒰.openCover)
  intro s
  have hsq := isPullback_away 𝒜 I (s.2 : A) s.2.2 s.1.2
  change IsClosedImmersion (pullback.snd (projMap 𝒜 I)
    (Proj.awayι 𝒜 (s.2 : A) s.2.2 s.1.2))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      hsq.flip.isoPullback.hom,
    hsq.flip.isoPullback_hom_snd]
  exact IsClosedImmersion.spec_of_surjective _
    (awayMap_surjective 𝒜 I (s.2 : A) s.2.2)

end Nat

end GradedIdealQuotient
