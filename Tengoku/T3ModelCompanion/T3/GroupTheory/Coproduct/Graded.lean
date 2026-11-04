/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Coproduct.Basic
public import Tengoku.T3ModelCompanion.T3.GroupTheory.Presentation
public import Tengoku.T3ModelCompanion.T3.GroupTheory.AssociatedGraded.Bracket
public import Tengoku.T3ModelCompanion.T3.GroupTheory.AssociatedGraded.Subgroup
public import Tengoku.Seed.LinearAlgebra.Prod
public import Tengoku.Seed.LinearAlgebra.TensorProduct.Map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical maps for the graded coproduct

The pure components are induced by the two factor inclusions. Mixed components are obtained
by descending their bilinear commutator to the tensor product. These maps do not choose bases.
The degree-one map is an isomorphism, with inverse induced by the factor retractions.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, v9 Proposition 4.4.
-/

@[expose] public section

open scoped TensorProduct

namespace T3.Coproduct

open AssociatedGraded

variable {G H : Type*} [Group G] [Group H]
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

/-- The sum of the two factor maps on a graded layer.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, pure components of `η`.-/
def factorMap (n : ℕ) : Layer G n × Layer H n →ₗ[ZMod 3] Layer (Coproduct G H) n :=
  (mapLayer inl n).coprod (mapLayer inr n)

/-- The pair of maps induced by the two factor retractions.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, inverse on pure components.-/
def factorProjection (n : ℕ) : Layer (Coproduct G H) n →ₗ[ZMod 3] Layer G n × Layer H n :=
  (mapLayer (fst Fact.out) n).prod (mapLayer (snd Fact.out) n)

omit [Fact (HasExponentThree H)] in
/--
@isnad1 id=eq.0h4v.s10.125f8e883f64 from=translated src=- shape=91a70360 vocab=0b340de1
-/
@[simp]
theorem mapLayer_fst_inl (n : ℕ) (x : Layer G n) :
    mapLayer (fst (H := H) Fact.out) n (mapLayer inl n x) = x := by
  rw [← LinearMap.comp_apply, ← mapLayer_comp, fst_comp_inl, mapLayer_id]
  rfl

/--
@isnad1 id=eq.0h4v.s10.cf339b9f04de from=translated src=- shape=0f182a75 vocab=6436d387
-/
@[simp]
theorem mapLayer_fst_inr (n : ℕ) (x : Layer H n) :
    mapLayer (fst (G := G) Fact.out) n (mapLayer inr n x) = 0 := by
  rw [← LinearMap.comp_apply, ← mapLayer_comp, fst_comp_inr, mapLayer_one]
  rfl

/--
@isnad1 id=eq.0h4v.s10.13d1fbdfb734 from=translated src=- shape=175c1d17 vocab=dcf540fc
-/
@[simp]
theorem mapLayer_snd_inl (n : ℕ) (x : Layer G n) :
    mapLayer (snd (H := H) Fact.out) n (mapLayer inl n x) = 0 := by
  rw [← LinearMap.comp_apply, ← mapLayer_comp, snd_comp_inl, mapLayer_one]
  rfl

omit [Fact (HasExponentThree G)] in
/--
@isnad1 id=eq.0h4v.s10.17b37139364f from=translated src=- shape=5d1b352f vocab=4d651934
-/
@[simp]
theorem mapLayer_snd_inr (n : ℕ) (x : Layer H n) :
    mapLayer (snd (G := G) Fact.out) n (mapLayer inr n x) = x := by
  rw [← LinearMap.comp_apply, ← mapLayer_comp, snd_comp_inr, mapLayer_id]
  rfl

/--
@isnad1 id=eq.0h4v.s11.3bc77c49a443 from=translated src=- shape=913dd889 vocab=dddadc26
-/
@[simp]
theorem factorMap_inl (n : ℕ) (x : Layer G n) :
    factorMap n (x, (0 : Layer H n)) = mapLayer inl n x := by
  simp [factorMap]

/--
@isnad1 id=eq.0h4v.s11.9b7a99f8456c from=translated src=- shape=7dd0b803 vocab=acb01f51
-/
@[simp]
theorem factorMap_inr (n : ℕ) (x : Layer H n) :
    factorMap n ((0 : Layer G n), x) = mapLayer inr n x := by
  simp [factorMap]

/--
@isnad1 id=eq.0h4v.s11.a58e81d59628 from=translated src=- shape=59cf8ae1 vocab=9d299809
-/
@[simp]
theorem factorProjection_inl (n : ℕ) (x : Layer G n) :
    factorProjection n (mapLayer (inl (H := H)) n x) = (x, 0) := by
  simp [factorProjection]

/--
@isnad1 id=eq.0h4v.s11.8d745e1ce26f from=translated src=- shape=7d962cef vocab=f2bd0518
-/
@[simp]
theorem factorProjection_inr (n : ℕ) (x : Layer H n) :
    factorProjection n (mapLayer (inr (G := G)) n x) = (0, x) := by
  simp [factorProjection]

/-- The two factor components embed as a direct sum in every graded layer.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, pure components.
@isnad1 id=eq.0h4v.s11.8d838798e1b8 from=translated src=- shape=5045ba05 vocab=bb9477f4
-/
@[simp]
theorem factorProjection_factorMap (n : ℕ) (x : Layer G n × Layer H n) :
    factorProjection n (factorMap n x) = x := by
  simp [factorMap, factorProjection]

/-- Injectivity of the sum of the pure factor components, without finite generation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, pure components.
@isnad1 id=injectiv.0h3v.s10.71eb904e8d91 from=translated src=- shape=85b754cd vocab=e24886a9
-/
theorem factorMap_injective (n : ℕ) : Function.Injective (factorMap (G := G) (H := H) n) :=
  (show Function.LeftInverse (factorProjection n) (factorMap (G := G) (H := H) n) from
    factorProjection_factorMap n).injective

/-- In degree one the two factor components exhaust the coproduct's quotient.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, degree-one identification.
@isnad1 id=eq.0h3v.s11.25625b60a3a9 from=translated src=- shape=98f99d7a vocab=bb9477f4
-/
@[simp]
theorem factorMap_one_factorProjection (x : Layer (Coproduct G H) 1) :
    factorMap 1 (factorProjection 1 x) = x := by
  let e := (factorMap (G := G) (H := H) 1).comp (factorProjection 1)
  let h : MulLayer (Coproduct G H) 1 →* MulLayer (Coproduct G H) 1 :=
    MonoidHom.toAdditive.symm e.toAddMonoidHom
  have hh : h.comp (quotientOne (Coproduct G H)) = quotientOne (Coproduct G H) := by
    apply hom_ext
    · intro a
      exact congrArg Additive.toMul
        (show factorMap 1 (factorProjection 1 (mapLayer (inl (H := H)) 1
          (mk G 1 ⟨a, Subgroup.mem_top _⟩))) =
            mapLayer inl 1 (mk G 1 ⟨a, Subgroup.mem_top _⟩) by
              rw [factorProjection_inl, factorMap_inl])
    · intro a
      exact congrArg Additive.toMul
        (show factorMap 1 (factorProjection 1 (mapLayer (inr (G := G)) 1
          (mk H 1 ⟨a, Subgroup.mem_top _⟩))) =
            mapLayer inr 1 (mk H 1 ⟨a, Subgroup.mem_top _⟩) by
              rw [factorProjection_inr, factorMap_inr])
  obtain ⟨a, rfl⟩ := mk_surjective (Coproduct G H) 1 x
  exact congrArg Additive.ofMul (DFunLike.congr_fun hh (a : Coproduct G H))

/-- The canonical degree-one isomorphism `η₁` of Proposition 4.4.
Its inverse consists of the two factor retractions.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, `η₁`.-/
def layerOneEquiv : (Layer G 1 × Layer H 1) ≃ₗ[ZMod 3] Layer (Coproduct G H) 1 :=
  { factorMap 1 with
    invFun := factorProjection 1
    left_inv := factorProjection_factorMap 1
    right_inv := factorMap_one_factorProjection }

/--
@isnad1 id=eq.0h3v.s12.09a173f47cb2 from=translated src=- shape=67d8d49e vocab=2aab6a3c
-/
@[simp]
theorem layerOneEquiv_apply (x : Layer G 1 × Layer H 1) :
    layerOneEquiv x = mapLayer inl 1 x.1 + mapLayer inr 1 x.2 := rfl

/--
@isnad1 id=eq.0h3v.s12.84527132fe27 from=translated src=- shape=3dd30e68 vocab=d1368dd2
-/
@[simp]
theorem layerOneEquiv_symm_apply (x : Layer (Coproduct G H) 1) :
    layerOneEquiv.symm x = (mapLayer (fst Fact.out) 1 x, mapLayer (snd Fact.out) 1 x) := rfl

omit [Fact (HasExponentThree H)] in
/-- The canonical left factor inclusion is strict for the lower central series.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, pure left component.
@isnad1 id=isstrict.0h2v.s7.8aa3a12e58d4 from=translated src=- shape=8638fa84 vocab=3319a08e
-/
theorem isStrict_inl : IsStrict (inl (G := G) (H := H)).range :=
  isStrict_range_of_leftInverse inl (fst Fact.out) rfl

omit [Fact (HasExponentThree G)] in
/-- The canonical right factor inclusion is strict for the lower central series.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, pure right component.
@isnad1 id=isstrict.0h2v.s7.c1f7a4615a52 from=translated src=- shape=e1dd7394 vocab=9ad77fb9
-/
theorem isStrict_inr : IsStrict (inr (G := G) (H := H)).range :=
  isStrict_range_of_leftInverse inr (snd Fact.out) rfl

/-- The mixed component of a positive graded layer, defined by the canonical commutator.
In particular the degree `(1,2)` component uses the bracket in the printed order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, the tensor formula for `η`.-/
def mixedMap {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Layer G i ⊗[ZMod 3] Layer H j →ₗ[ZMod 3] Layer (Coproduct G H) (i + j) :=
  TensorProduct.lift ((bracketLayer hi hj).compl₁₂ (mapLayer inl i) (mapLayer inr j))

/-- The mixed component sends a pure tensor to the bracket of its two factor images.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, defining tensor formula.
@isnad1 id=eq.2h6v.s13.a4cc0ec28b67 from=translated src=- shape=90c45eb2 vocab=ca010390
-/
@[simp]
theorem mixedMap_tmul {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : Layer G i) (y : Layer H j) :
    mixedMap hi hj (x ⊗ₜ[ZMod 3] y) =
      bracketLayer hi hj (mapLayer inl i x) (mapLayer inr j y) := rfl

/-- The three components in the domain of the paper's degree-two map, in printed order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, domain of `η₂`.-/
abbrev LayerTwoBlocks := Layer G 2 × (Layer G 1 ⊗[ZMod 3] Layer H 1) × Layer H 2

/-- The canonical map `η₂`, defined before proving that it is an isomorphism.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, `η₂`.-/
def layerTwoMap : LayerTwoBlocks (G := G) (H := H) →ₗ[ZMod 3] Layer (Coproduct G H) 2 :=
  (mapLayer inl 2).coprod ((mixedMap (by decide) (by decide)).coprod (mapLayer inr 2))

/-- The four components in the domain of the paper's degree-three map, in printed order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, domain of `η₃`.-/
abbrev LayerThreeBlocks := Layer G 3 × (Layer G 2 ⊗[ZMod 3] Layer H 1) ×
  (Layer G 1 ⊗[ZMod 3] Layer H 2) × Layer H 3

/-- The canonical map `η₃`, with the `(1,2)` component given by `[inl x, inr q]`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, `η₃`.-/
def layerThreeMap : LayerThreeBlocks (G := G) (H := H) →ₗ[ZMod 3] Layer (Coproduct G H) 3 :=
  (mapLayer inl 3).coprod ((mixedMap (by decide) (by decide)).coprod
    ((mixedMap (by decide) (by decide)).coprod (mapLayer inr 3)))

/--
@isnad1 id=eq.0h3v.s13.b07cacd6741b from=translated src=- shape=33902b1b vocab=a12d30c5
-/
theorem layerTwoMap_apply (x : LayerTwoBlocks (G := G) (H := H)) :
    layerTwoMap x = mapLayer inl 2 x.1 +
      (mixedMap (by decide) (by decide) x.2.1 + mapLayer inr 2 x.2.2) := rfl

/--
@isnad1 id=eq.0h3v.s14.66b631dbf632 from=translated src=- shape=be812275 vocab=adcdd6ad
-/
theorem layerThreeMap_apply (x : LayerThreeBlocks (G := G) (H := H)) :
    layerThreeMap x = mapLayer inl 3 x.1 +
      (mixedMap (by decide) (by decide) x.2.1 +
        (mixedMap (by decide) (by decide) x.2.2.1 + mapLayer inr 3 x.2.2.2)) := rfl

/-- A mixed tensor component is killed by the retraction onto either pure factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, mixed and pure components.
@isnad1 id=eq.2h4v.s11.5d9f93b561d0 from=translated src=- shape=b0020bde vocab=8f241963
-/
theorem factorProjection_comp_mixedMap {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    (factorProjection (G := G) (H := H) (i + j)).comp (mixedMap hi hj) = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, mixedMap_tmul, factorProjection, LinearMap.prod_apply,
    Function.prod_apply, mapLayer_bracketLayer, mapLayer_fst_inl, mapLayer_fst_inr,
    mapLayer_snd_inl, mapLayer_snd_inr, map_zero, LinearMap.zero_apply, Prod.zero_eq_mk]

variable {G' H' : Type*} [Group G'] [Group H']
  [Fact (HasExponentThree G')] [Fact (HasExponentThree H')]

omit [Fact (HasExponentThree H)] [Fact (HasExponentThree H')] in
/--
@isnad1 id=eq.0h8v.s11.f973b2cfa503 from=translated src=- shape=8961aaa7 vocab=d364d760
-/
@[simp]
theorem mapLayer_map_inl (f : G →* G') (g : H →* H') (n : ℕ) (x : Layer G n) :
    mapLayer (map f g) n (mapLayer inl n x) = mapLayer inl n (mapLayer f n x) := by
  rw [← LinearMap.comp_apply, ← mapLayer_comp, map_comp_inl, mapLayer_comp]
  rfl

omit [Fact (HasExponentThree G)] [Fact (HasExponentThree G')] in
/--
@isnad1 id=eq.0h8v.s11.4389b0187f70 from=translated src=- shape=771ead06 vocab=2a3b08e4
-/
@[simp]
theorem mapLayer_map_inr (f : G →* G') (g : H →* H') (n : ℕ) (x : Layer H n) :
    mapLayer (map f g) n (mapLayer inr n x) = mapLayer inr n (mapLayer g n x) := by
  rw [← LinearMap.comp_apply, ← mapLayer_comp, map_comp_inr, mapLayer_comp]
  rfl

/-- Naturality of the sum of the pure components in every degree.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, naturality of the pure maps.
@isnad1 id=eq.0h8v.s12.8c4fb3e3656c from=translated src=- shape=2b1f64bc vocab=2e827ec9
-/
theorem mapLayer_factorMap (f : G →* G') (g : H →* H') (n : ℕ)
    (x : Layer G n × Layer H n) :
    mapLayer (map f g) n (factorMap n x) =
      factorMap n (mapLayer f n x.1, mapLayer g n x.2) := by
  simp [factorMap]

/-- The degree-one isomorphism is natural in both factors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, naturality of `η₁`.
@isnad1 id=eq.0h7v.s12.ea96c4cc3d1d from=translated src=- shape=92e74920 vocab=86144785
-/
theorem layerOneEquiv_natural (f : G →* G') (g : H →* H') (x : Layer G 1 × Layer H 1) :
    mapLayer (map f g) 1 (layerOneEquiv x) =
      layerOneEquiv (mapLayer f 1 x.1, mapLayer g 1 x.2) :=
  mapLayer_factorMap f g 1 x

/-- Naturality of the mixed tensor component as an equality of linear maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, naturality of the tensor maps.
@isnad1 id=eq.2h8v.s11.f4a28b494b59 from=translated src=- shape=5f7e9e35 vocab=62c66ea0
-/
theorem mapLayer_comp_mixedMap (f : G →* G') (g : H →* H') {i j : ℕ}
    (hi : 0 < i) (hj : 0 < j) :
    (mapLayer (map f g) (i + j)).comp (mixedMap hi hj) =
      (mixedMap hi hj).comp (TensorProduct.map (mapLayer f i) (mapLayer g j)) := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, mixedMap_tmul, TensorProduct.map_tmul,
    mapLayer_bracketLayer, mapLayer_map_inl, mapLayer_map_inr]

/-- Naturality of a mixed tensor component, evaluated on an arbitrary tensor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, naturality of the tensor maps.
@isnad1 id=eq.2h9v.s12.9e4bb858f441 from=translated src=- shape=91567cd2 vocab=ef661e4e
-/
theorem mapLayer_mixedMap (f : G →* G') (g : H →* H') {i j : ℕ}
    (hi : 0 < i) (hj : 0 < j) (x : Layer G i ⊗[ZMod 3] Layer H j) :
    mapLayer (map f g) (i + j) (mixedMap hi hj x) =
      mixedMap hi hj (TensorProduct.map (mapLayer f i) (mapLayer g j) x) :=
  DFunLike.congr_fun (mapLayer_comp_mixedMap f g hi hj) x

/-- Naturality of the entire degree-two map, including its mixed tensor component.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, naturality of `η₂`.
@isnad1 id=eq.0h7v.s13.1b9331834684 from=translated src=- shape=143199b9 vocab=a79bc2b8
-/
theorem layerTwoMap_natural (f : G →* G') (g : H →* H')
    (x : LayerTwoBlocks (G := G) (H := H)) :
    mapLayer (map f g) 2 (layerTwoMap x) = layerTwoMap
      (mapLayer f 2 x.1, TensorProduct.map (mapLayer f 1) (mapLayer g 1) x.2.1,
        mapLayer g 2 x.2.2) := by
  simp only [layerTwoMap_apply, map_add, mapLayer_map_inl, mapLayer_map_inr,
    mapLayer_mixedMap (i := 1) (j := 1)]

/-- Naturality of the entire degree-three map, with both mixed components in printed order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, naturality of `η₃`.
@isnad1 id=eq.0h7v.s14.05aead6983d1 from=translated src=- shape=711e5668 vocab=82c0d81a
-/
theorem layerThreeMap_natural (f : G →* G') (g : H →* H')
    (x : LayerThreeBlocks (G := G) (H := H)) :
    mapLayer (map f g) 3 (layerThreeMap x) = layerThreeMap
      (mapLayer f 3 x.1, TensorProduct.map (mapLayer f 2) (mapLayer g 1) x.2.1,
        TensorProduct.map (mapLayer f 1) (mapLayer g 2) x.2.2.1, mapLayer g 3 x.2.2.2) := by
  simp only [layerThreeMap_apply, map_add, mapLayer_map_inl, mapLayer_map_inr,
    mapLayer_mixedMap (i := 2) (j := 1), mapLayer_mixedMap (i := 1) (j := 2)]

end T3.Coproduct
