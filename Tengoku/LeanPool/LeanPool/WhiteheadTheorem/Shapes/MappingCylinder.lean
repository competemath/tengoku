/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Tengoku.LeanPool.LeanPool.WhiteheadTheorem.Defs
public import Tengoku.LeanPool.LeanPool.WhiteheadTheorem.Exponential
public import Tengoku.LeanPool.LeanPool.WhiteheadTheorem.Shapes.Maps
public import Tengoku.LeanPool.LeanPool.WhiteheadTheorem.Shapes.Pushout
public import Tengoku.LeanPool.LeanPool.WhiteheadTheorem.Shapes.UnitInterval
public import Tengoku

/-!
# LeanPool.WhiteheadTheorem.Shapes.MappingCylinder

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.MappingCylinder`.
-/

@[expose] public section

open CategoryTheory
open scoped unitInterval ContinuousMap

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

namespace TopCat

/-- The mapping cylinder of a continuous map `f : X ⟶ Y`. -/
noncomputable def MapCyl : TopCat.{u} := Limits.pushout f (Cyl.i₀ X)

namespace MapCyl

/-- `inl` -/
noncomputable abbrev inl : Y ⟶ MapCyl f := Limits.pushout.inl _ _
/-- `inr` -/
noncomputable abbrev inr : TopCat.of (X × I) ⟶ MapCyl f := Limits.pushout.inr _ _
/-- `condition`
@isnad1 id=eq.0h3v.s6.bb776d884d0e from=translated src=- shape=958850f1 vocab=22ae1235
-/
lemma condition : f ≫ inl f = Cyl.i₀ X ≫ inr f := Limits.pushout.condition

/-- Inclusion map from the domain `X` to the mapping cylinder of `f : X ⟶ Y` -/
noncomputable abbrev domIncl : X ⟶ MapCyl f := Cyl.i₁ X ≫ inr f

/-- Inclusion map from the codomain `Y` to the mapping cylinder of `f : X ⟶ Y` -/
noncomputable alias codIncl := inl

/-- The top surface of the mapping cylinder -/
abbrev top : Set (MapCyl f) := Set.range (domIncl f)

/--
@isnad1 id=eq.0h3v.s9.d9efbef0cf61 from=translated src=- shape=c0471a51 vocab=e0fceb23
-/
lemma domIncl_hom_eq_pushoutInr'_comp :
    (domIncl f).hom = (pushoutInr' _ _).comp (Cyl.i₁ToComplRangeI₀ X) := by
  ext x
  simp_all only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rfl

/--
@isnad1 id=isembedd.0h3v.s6.06c343cabb7e from=translated src=- shape=42e09575 vocab=85532317
-/
theorem isEmbedding_domIncl : Topology.IsEmbedding (domIncl f) := by
  change Topology.IsEmbedding ((domIncl f).hom)
  rw [domIncl_hom_eq_pushoutInr'_comp]
  have em_inr : Topology.IsOpenEmbedding (pushoutInr' f (Cyl.i₀ X)) := by
    apply isOpenEmbedding_pushoutInr'
    apply Cyl.isClosed_range_i₀
  have em_i₁ : Topology.IsClosedEmbedding (Cyl.i₁ToComplRangeI₀ X) :=
    Cyl.isClosedEmbedding_i₁ToComplRangeI₀ X
  convert em_inr.toIsEmbedding.comp em_i₁.toIsEmbedding using 2
  · rfl
  · rfl
  · exact heq_of_eq (ContinuousMap.coe_comp _ _)

/-- The domain `X` of a continuous map `f` is homeomorphic to the top surface of
the mapping cylinder of `f`. -/
noncomputable def domHomeoTop : X ≃ₜ top f := (isEmbedding_domIncl f).toHomeomorph

/-- `domInclToTop` -/
noncomputable def domInclToTop : C(X, top f) := toContinuousMap (domHomeoTop f)
/-- `domInclFromTop` -/
def domInclFromTop : C(top f, MapCyl f) := ⟨Subtype.val, continuous_subtype_val⟩

/--
@isnad1 id=eq.0h3v.s6.05ee05e2fb90 from=translated src=- shape=42331259 vocab=b29545b6
-/
lemma domIncl_hom_eq_domInclFromTop_comp_domInclToTop :
  (domIncl f).hom = (domInclFromTop f).comp (domInclToTop f) := rfl
/--
@isnad1 id=eq.0h3v.s8.a57495107fc9 from=translated src=- shape=1241efaa vocab=e206d7e6
-/
lemma domIncl_toFun_eq_domInclFromTop_comp_domInclToTop :
  (domIncl f).hom.toFun = domInclFromTop f ∘ domInclToTop f := rfl

/--
@isnad1 id=ishomeom.0h3v.s7.e80e85dedbe2 from=translated src=- shape=2cb04f47 vocab=4e109cd3
-/
lemma isHomeomorph_domInclToTop : IsHomeomorph (domInclToTop f) :=
  isHomeomorph_iff_exists_homeomorph.mpr ⟨domHomeoTop f, rfl⟩

/-- The retraction from a mapping cylinder of `f : X ⟶ Y` to its base `Y` -/
noncomputable def retr : MapCyl f ⟶ Y :=
  Limits.pushout.desc (𝟙 Y) (Cyl.r₀ X ≫ f)
    (by rw [Category.comp_id, ← Category.assoc, Cyl.i₀_r₀_eq_id, Category.id_comp])

/--
@isnad1 id=eq.0h3v.s5.d7935c5c4085 from=translated src=- shape=587e4121 vocab=e78b34c6
-/
lemma domIncl_retr_eq : domIncl f ≫ retr f = f := by
  unfold domIncl retr
  change Cyl.i₁ X ≫ Limits.pushout.inr f (Cyl.i₀ X) ≫ _ = f
  rw [Limits.pushout.inr_desc, ← Category.assoc, Cyl.i₁_r₀_eq_id, Category.id_comp]
/--
@isnad1 id=eq.0h5v.s6.3d93fc1a4baa from=translated src=- shape=ff821992 vocab=e78b34c6
-/
lemma domIncl_retr_eq_assoc : domIncl f ≫ retr f ≫ h = f ≫ h := by
  rw [← Category.assoc, domIncl_retr_eq f]

/--
@isnad1 id=eq.0h3v.s5.2abfc770d46d from=translated src=- shape=128fc6cf vocab=483fbc6c
-/
lemma inl_retr_eq_id : inl f ≫ retr f = 𝟙 Y := by
  change Limits.pushout.inl f (Cyl.i₀ X) ≫ _ = _
  rw [retr, Limits.pushout.inl_desc]
/--
@isnad1 id=eq.0h3v.s5.5d4d2698b17c from=translated src=- shape=128fc6cf vocab=8827f97b
-/
lemma codIncl_retr_eq_id : codIncl f ≫ retr f = 𝟙 Y := inl_retr_eq_id f
-- alias codIncl_retr_eq_id := inl_retr_eq_id

/-- The curried form of the deformation retraction
from a mapping cylinder of `f : X ⟶ Y` to its base `Y`.
This is a curried homotopy from `retr f ≫ inl f` (when `t = 0`) to `𝟙 (MapCyl f)` (when `t = 1`).
The curried form facilitates the proof of continuity (see `MapCyl.equivBase.left_inv`),
and is equal to uncurried form when evaluated at any `t : I`
(see `curriedDeformRetrEvalAt_eq_deformRetrEvalAt`).

Note: `s * t` uses the instance `unitInterval.continuousMul` in `Shapes/Maps.lean`. -/
noncomputable def curriedDeformRetr : MapCyl f ⟶ TopCat.of C(I, MapCyl f) :=
  Limits.pushout.desc (PathSpace.homToConstPaths (inl f))
    (ofHom <| ContinuousMap.curry
      { toFun := fun ⟨⟨x, s⟩, t⟩ ↦ (inr f).hom ⟨x, s * t⟩
        continuous_toFun := by fun_prop } )
    (by
      simp only [PathSpace.homToConstPaths]
      ext x t
      simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.curry_apply,
        ContinuousMap.coe_mk, zero_mul]
      exact congr_fun (congr_arg (ContinuousMap.toFun ∘ Hom.hom) (condition f)) x )

/-- `curriedDeformRetrEvalAt` -/
noncomputable def curriedDeformRetrEvalAt (t : I) : MapCyl f ⟶ MapCyl f :=
  ofHom <| (curriedDeformRetr f).hom.uncurry.curryLeft t

/--
@isnad1 id=eq.0h5v.s9.cd7a76907db7 from=translated src=- shape=bbd7e8d8 vocab=1be80cbb
-/
lemma curriedDeformRetrEvalAt_hom_apply (t : I) (z : MapCyl f) :
    (curriedDeformRetrEvalAt f t).hom z = ((curriedDeformRetr f).hom z) t :=
  rfl

/-- The homotopy (deformation retraction)
from `retr f ≫ inl f` (when `t = 0`) to `𝟙 (MapCyl f)` (when `t = 1`),
evaluated at `t`. -/
noncomputable def deformRetrEvalAt (t : I) : MapCyl f ⟶ MapCyl f :=
  Limits.pushout.desc (inl f)
    (ofHom (ContinuousMap.id _ |>.prodMap <| ContinuousMap.mulRight t) ≫ inr f)
    -- fun ⟨x, s⟩ ↦ (inr f).hom ⟨x, s * t⟩
    (by
      ext x
      simp only [hom_comp, ContinuousMap.comp_apply, hom_ofHom, ContinuousMap.comp_assoc,
        ContinuousMap.coe_mk, ContinuousMap.prodMap_apply, ContinuousMap.coe_id,
        ContinuousMap.coe_mulRight, Prod.map_apply, id_eq, zero_mul]
      exact congr_fun (congr_arg (ContinuousMap.toFun ∘ Hom.hom) (condition f)) x )

/--
@isnad1 id=eq.0h3v.s6.9d2bc7cfe56e from=translated src=- shape=c51d782f vocab=3ec8a105
-/
lemma deformRetrEvalAt_zero : deformRetrEvalAt f 0 = retr f ≫ inl f := by
  simp only [deformRetrEvalAt, ContinuousMap.mulRight_zero]
  apply Limits.pushout.hom_ext
  · rw [Limits.pushout.inl_desc, retr]
    change inl f = Limits.pushout.inl f (Cyl.i₀ X) ≫ Limits.pushout.desc (𝟙 Y) (Cyl.r₀ X ≫ f) _ ≫ _
    rw [Limits.pushout.inl_desc_assoc, Category.id_comp]
  · rw [Limits.pushout.inr_desc, retr]
    change ofHom ((ContinuousMap.id ↑X).prodMap (ContinuousMap.const (↑I) 0)) ≫ inr f =
      Limits.pushout.inr f (Cyl.i₀ X) ≫ Limits.pushout.desc (𝟙 Y) (Cyl.r₀ X ≫ f) _ ≫ _
    rw [Limits.pushout.inr_desc_assoc, Category.assoc, condition f, ← Category.assoc]
    congr

/--
@isnad1 id=eq.0h3v.s5.07b4e0d604e1 from=translated src=- shape=3c2ffa39 vocab=a7545fbd
-/
lemma deformRetrEvalAt_one : deformRetrEvalAt f 1 = 𝟙 _ := by
  simp only [deformRetrEvalAt, ContinuousMap.mulRight_one]
  apply Limits.pushout.desc_inl_inr

/--
@isnad1 id=eq.0h4v.s5.e7e10a0dafd5 from=translated src=- shape=d5d1c493 vocab=aad6d793
-/
lemma curriedDeformRetrEvalAt_eq_deformRetrEvalAt (t : I) :
    curriedDeformRetrEvalAt f t = deformRetrEvalAt f t := by
  apply Limits.pushout.hom_ext
  · rw [deformRetrEvalAt, Limits.pushout.inl_desc]
    ext y
    change ((inl f ≫ curriedDeformRetr f) y) t = _  -- curriedDeformRetrEvalAt_hom_apply
    rw [curriedDeformRetr]
    change ((ConcreteCategory.hom (Limits.pushout.inl f (Cyl.i₀ X) ≫
        Limits.pushout.desc (PathSpace.homToConstPaths (inl f)) _ _)) y) t = _
    rw [Limits.pushout.inl_desc]
    simp_all
  · rw [deformRetrEvalAt, Limits.pushout.inr_desc]
    ext z
    simp only [hom_comp, ContinuousMap.comp_apply, hom_ofHom, ContinuousMap.prodMap_apply,
      ContinuousMap.coe_id, ContinuousMap.coe_mulRight]
    change ((inr f ≫ curriedDeformRetr f) z) t = _
    rw [curriedDeformRetr]
    change ((ConcreteCategory.hom (Limits.pushout.inr f (Cyl.i₀ X) ≫
        Limits.pushout.desc (PathSpace.homToConstPaths (inl f)) _ _)) z) t = _
    rw [Limits.pushout.inr_desc]
    congr

/-- The mapping cylinder of `f : X ⟶ Y` is homotopy equivalent to its base `Y`. -/
noncomputable def homotopyEquivBase : MapCyl f ≃ₕ Y where
  toFun := (retr f).hom
  invFun := (inl f).hom
  left_inv := Nonempty.intro
    { toContinuousMap := (curriedDeformRetr f).hom.uncurry.argSwap
      map_zero_left z := by
        simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
          ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
          Function.uncurry_apply_pair]
        rw [← curriedDeformRetrEvalAt_hom_apply, curriedDeformRetrEvalAt_eq_deformRetrEvalAt]
        rw [deformRetrEvalAt_zero, hom_comp, ContinuousMap.comp_apply]
      map_one_left z := by
        simp only [ContinuousMap.argSwap, ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
          ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply, ContinuousMap.uncurry_apply,
          Function.uncurry_apply_pair, ContinuousMap.id_apply]
        rw [← curriedDeformRetrEvalAt_hom_apply, curriedDeformRetrEvalAt_eq_deformRetrEvalAt]
        rw [deformRetrEvalAt_one, hom_id, ContinuousMap.id_apply] }
  right_inv := by rw [← hom_comp, inl_retr_eq_id, hom_id]

/-!
TODO: Show `inl f` is a topological embedding using `inl f ≫ retr f = 𝟙 Y`, i.e.,
using `homotopyEquivBase.right_inv`.
-/

/--
@isnad1 id=ishomoto.0h3v.s5.967ee171d762 from=translated src=- shape=781c3749 vocab=eaf164cf
-/
theorem isHomotopyEquiv_retr : IsHomotopyEquiv (retr f).hom :=
  ⟨homotopyEquivBase f, rfl⟩

end MapCyl

end TopCat
