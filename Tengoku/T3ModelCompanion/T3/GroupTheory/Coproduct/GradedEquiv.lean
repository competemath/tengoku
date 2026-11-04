/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Coproduct.QuotientMaps
public import Tengoku.T3ModelCompanion.T3.LinearAlgebra.LinearMapQuotient
public import Tengoku.Seed.Algebra.Field.ZMod
public import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The canonical graded coproduct isomorphisms

Choose a basis of each factor's first layer and lift its basis vectors to group elements.
The resulting free presentations have kernel in the derived subgroup. The free exterior
decomposition descends through their relation spaces, since the block kernels map onto exactly
the graded images of the combined normal closure. This proves bijectivity of the canonical
maps already defined in `Coproduct.Graded`, for arbitrary groups and arbitrary rank.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 1, lines 939–1022.
-/

@[expose] public section

namespace T3.Coproduct

open AssociatedGraded Module

variable {G H : Type*} [Group G] [Group H]
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

private theorem layerTwoMap_bijective_of_presentations {I J : Type*}
    (f : Free I →* G) (g : Free J →* H) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hKf : f.ker ≤ commutator (Free I))
    (hKg : g.ker ≤ commutator (Free J)) :
    Function.Bijective (layerTwoMap (G := G) (H := H)) := by
  have hp := Presentation.presentationMap_surjective f g hf hg
  apply LinearMap.bijective_of_bijective_of_ker_map freeSumLayerTwoMap
    (layerTwoBlockMap f g) (mapLayer (Presentation.presentationMap f g) 2) layerTwoMap
    freeSumLayerTwoMap_bijective (layerTwoBlockMap_surjective f g hf hg)
    (mapLayer_surjective _ hp 2) (freeSumLayerTwoMap_quotient_square f g)
  rw [mapLayer_ker _ hp, Presentation.presentationMap_ker f g hf hg]
  exact (layerTwoBlockMap_ker_map_freeSum f g hf hg hKf hKg).symm

private theorem layerThreeMap_bijective_of_presentations {I J : Type*}
    (f : Free I →* G) (g : Free J →* H) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hKf : f.ker ≤ commutator (Free I))
    (hKg : g.ker ≤ commutator (Free J)) :
    Function.Bijective (layerThreeMap (G := G) (H := H)) := by
  have hp := Presentation.presentationMap_surjective f g hf hg
  apply LinearMap.bijective_of_bijective_of_ker_map freeSumLayerThreeMap
    (layerThreeBlockMap f g) (mapLayer (Presentation.presentationMap f g) 3) layerThreeMap
    freeSumLayerThreeMap_bijective (layerThreeBlockMap_surjective f g hf hg)
    (mapLayer_surjective _ hp 3) (freeSumLayerThreeMap_quotient_square f g)
  rw [mapLayer_ker _ hp, Presentation.presentationMap_ker f g hf hg]
  exact (layerThreeBlockMap_ker_map_freeSum f g hf hg hKf hKg).symm

universe u

private theorem exists_basis_presentation (G : Type u) [Group G]
    [Fact (HasExponentThree G)] :
    ∃ (I : Type u) (f : Free I →* G),
      Function.Surjective f ∧ f.ker ≤ commutator (Free I) := by
  classical
  have hG : HasExponentThree G := Fact.out
  let b := Basis.ofVectorSpace (ZMod 3) (Layer G 1)
  let a := fun i => ((mk_surjective G 1 (b i)).choose : G)
  have ha : ∀ i, mk G 1 ⟨a i, Subgroup.mem_top _⟩ = b i :=
    fun i => (mk_surjective G 1 (b i)).choose_spec
  exact ⟨_, Free.lift hG a, Free.presentation_of_basis hG b a ha⟩

/-- The canonical degree-two coproduct map is bijective for arbitrary exponent-three groups.
Its mixed component is the bracket of the factor inclusions on pure tensors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, bijectivity of `η₂`.
@isnad1 id=bijectiv.0h2v.s11.9d186ec3bba0 from=translated src=- shape=21c8cb98 vocab=e587284a
-/
theorem layerTwoMap_bijective : Function.Bijective (layerTwoMap (G := G) (H := H)) := by
  obtain ⟨I, f, hf, hKf⟩ := exists_basis_presentation G
  obtain ⟨J, g, hg, hKg⟩ := exists_basis_presentation H
  exact layerTwoMap_bijective_of_presentations f g hf hg hKf hKg

/-- The canonical degree-three coproduct map is bijective for arbitrary exponent-three groups.
The `(1,2)` component retains the paper's bracket order and its corresponding exterior sign.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, bijectivity of `η₃`.
@isnad1 id=bijectiv.0h2v.s12.25ed915e34d6 from=translated src=- shape=21c8cb98 vocab=ca724293
-/
theorem layerThreeMap_bijective : Function.Bijective (layerThreeMap (G := G) (H := H)) := by
  obtain ⟨I, f, hf, hKf⟩ := exists_basis_presentation G
  obtain ⟨J, g, hg, hKg⟩ := exists_basis_presentation H
  exact layerThreeMap_bijective_of_presentations f g hf hg hKf hKg

/-- **Proposition 4.4(1), degree two.** The canonical isomorphism `η₂`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, `η₂`.-/
noncomputable def layerTwoEquiv :
    LayerTwoBlocks (G := G) (H := H) ≃ₗ[ZMod 3] Layer (Coproduct G H) 2 :=
  LinearEquiv.ofBijective layerTwoMap layerTwoMap_bijective

/-- **Proposition 4.4(1), degree three.** The canonical isomorphism `η₃`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, `η₃`.-/
noncomputable def layerThreeEquiv :
    LayerThreeBlocks (G := G) (H := H) ≃ₗ[ZMod 3] Layer (Coproduct G H) 3 :=
  LinearEquiv.ofBijective layerThreeMap layerThreeMap_bijective

/-- The isomorphism has the previously specified canonical degree-two map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, canonical `η₂`.
@isnad1 id=eq.0h3v.s13.48694b8198ea from=translated src=- shape=8f5b3f91 vocab=2cd7373f
-/
@[simp]
theorem layerTwoEquiv_apply (x : LayerTwoBlocks (G := G) (H := H)) :
    layerTwoEquiv x = layerTwoMap x := rfl

/-- The isomorphism has the previously specified canonical degree-three map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, canonical `η₃`.
@isnad1 id=eq.0h3v.s14.b3c493792b13 from=translated src=- shape=8f5b3f91 vocab=b723f7bf
-/
@[simp]
theorem layerThreeEquiv_apply (x : LayerThreeBlocks (G := G) (H := H)) :
    layerThreeEquiv x = layerThreeMap x := rfl

/-- The degree-two inverse reads the left pure component in its first coordinate.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, canonical `η₂`.
@isnad1 id=eq.0h3v.s13.71c9d14172b2 from=translated src=- shape=1ecc1d83 vocab=421cd966
-/
@[simp]
theorem layerTwoEquiv_symm_inl (x : Layer G 2) :
    (layerTwoEquiv (G := G) (H := H)).symm (mapLayer inl 2 x) = (x, 0, 0) := by
  apply (layerTwoEquiv (G := G) (H := H)).injective
  simp only [LinearEquiv.apply_symm_apply, layerTwoEquiv_apply, layerTwoMap_apply,
    map_zero, add_zero]

/-- The degree-two inverse reads the tensor component in its middle coordinate.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, canonical `η₂`.
@isnad1 id=eq.0h3v.s13.c327df09aa25 from=translated src=- shape=4542f011 vocab=9fa8c3f8
-/
@[simp]
theorem layerTwoEquiv_symm_mixed (x : TensorProduct (ZMod 3) (Layer G 1) (Layer H 1)) :
    (layerTwoEquiv (G := G) (H := H)).symm
      (mixedMap (by decide) (by decide) x) = (0, x, 0) := by
  apply (layerTwoEquiv (G := G) (H := H)).injective
  simp only [LinearEquiv.apply_symm_apply, layerTwoEquiv_apply, layerTwoMap_apply,
    map_zero, add_zero, zero_add]

/-- The degree-two inverse reads the right pure component in its last coordinate.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, canonical `η₂`.
@isnad1 id=eq.0h3v.s13.5a665edcdb1c from=translated src=- shape=ff9f1dea vocab=28135f58
-/
@[simp]
theorem layerTwoEquiv_symm_inr (x : Layer H 2) :
    (layerTwoEquiv (G := G) (H := H)).symm (mapLayer inr 2 x) = (0, 0, x) := by
  apply (layerTwoEquiv (G := G) (H := H)).injective
  simp only [LinearEquiv.apply_symm_apply, layerTwoEquiv_apply, layerTwoMap_apply,
    map_zero, zero_add]

/-- The degree-three inverse reads the left pure component in its first coordinate.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, canonical `η₃`.
@isnad1 id=eq.0h3v.s13.fa079568a72e from=translated src=- shape=f6eb5f54 vocab=e71296c6
-/
@[simp]
theorem layerThreeEquiv_symm_inl (x : Layer G 3) :
    (layerThreeEquiv (G := G) (H := H)).symm (mapLayer inl 3 x) = (x, 0, 0, 0) := by
  apply (layerThreeEquiv (G := G) (H := H)).injective
  simp only [LinearEquiv.apply_symm_apply, layerThreeEquiv_apply, layerThreeMap_apply,
    map_zero, add_zero]

/-- The degree-three inverse reads the `(2,1)` tensor in its second coordinate.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, canonical `η₃`.
@isnad1 id=eq.0h3v.s14.e629952e7c03 from=translated src=- shape=8028b955 vocab=c13f1223
-/
@[simp]
theorem layerThreeEquiv_symm_mixed_two_one
    (x : TensorProduct (ZMod 3) (Layer G 2) (Layer H 1)) :
    (layerThreeEquiv (G := G) (H := H)).symm
      (mixedMap (i := 2) (j := 1) (by decide) (by decide) x) = (0, x, 0, 0) := by
  apply (layerThreeEquiv (G := G) (H := H)).injective
  simp only [LinearEquiv.apply_symm_apply, layerThreeEquiv_apply, layerThreeMap_apply,
    map_zero, add_zero, zero_add]

/-- The degree-three inverse reads the `(1,2)` tensor in its third coordinate, with the
canonical bracket order already included in the map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, canonical `η₃`.
@isnad1 id=eq.0h3v.s14.afd12bc4ce50 from=translated src=- shape=044cbdb9 vocab=c13f1223
-/
@[simp]
theorem layerThreeEquiv_symm_mixed_one_two
    (x : TensorProduct (ZMod 3) (Layer G 1) (Layer H 2)) :
    (layerThreeEquiv (G := G) (H := H)).symm
      (mixedMap (i := 1) (j := 2) (by decide) (by decide) x) = (0, 0, x, 0) := by
  apply (layerThreeEquiv (G := G) (H := H)).injective
  simp only [LinearEquiv.apply_symm_apply, layerThreeEquiv_apply, layerThreeMap_apply,
    map_zero, add_zero, zero_add]

/-- The degree-three inverse reads the right pure component in its last coordinate.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, canonical `η₃`.
@isnad1 id=eq.0h3v.s13.29974e5ff669 from=translated src=- shape=7ca622a9 vocab=49cf0cf0
-/
@[simp]
theorem layerThreeEquiv_symm_inr (x : Layer H 3) :
    (layerThreeEquiv (G := G) (H := H)).symm (mapLayer inr 3 x) = (0, 0, 0, x) := by
  apply (layerThreeEquiv (G := G) (H := H)).injective
  simp only [LinearEquiv.apply_symm_apply, layerThreeEquiv_apply, layerThreeMap_apply,
    map_zero, zero_add]

end T3.Coproduct
