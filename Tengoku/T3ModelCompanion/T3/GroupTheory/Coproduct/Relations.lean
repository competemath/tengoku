/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Coproduct.Presentation
public import Tengoku.T3ModelCompanion.T3.GroupTheory.AssociatedGraded.Subgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The graded relations of a coproduct presentation

The two free factors are retracts of the free group on their disjoint union. Thus the ambient
graded images of their relations are the images of the corresponding subspaces computed in
each factor. The normal-closure formulas then give the relation spaces in degrees two and three.
Normality of a factor relation subgroup absorbs its brackets with that same factor into its
third-degree relation space. No finite-rank or homogeneous-relation assumption is used.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof lines 971–1022.
-/

@[expose] public section

open scoped commutatorElement

namespace T3.AssociatedGraded

variable {G H : Type*} [Group G] [Group H]
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

/-- A normal subgroup's ambient graded image is closed under brackets with ambient layers.

In degrees two and one this is the paper's inclusion `Rₙ ∧ Vₙ ⊆ Sₙ`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof line 1010.
@isnad1 id=le.2h4v.s9.7bb09930308d from=translated src=- shape=d4f1d9f6 vocab=65c33770
-/
theorem bracketLayer_subgroupImage_top_le (K : Subgroup G) [K.Normal]
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Submodule.map₂ (bracketLayer hi hj) (subgroupImage K i) ⊤ ≤ subgroupImage K (i + j) := by
  apply Submodule.map₂_le.mpr
  intro x hx y _
  obtain ⟨x, hxK, rfl⟩ := (mem_subgroupImage K i x).mp hx
  obtain ⟨y, rfl⟩ := mk_surjective G j y
  exact (mem_subgroupImage K (i + j) _).mpr
    ⟨termCommutator hi hj x y,
      Subgroup.commutator_le_left K ⊤
        (Subgroup.commutator_mem_commutator hxK (Subgroup.mem_top _)), rfl⟩

/-- The same-factor brackets remain absorbed after applying any ambient group homomorphism.

The relation subgroup need only be normal in the source factor, not in the target group.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof line 1010.
@isnad1 id=le.2h6v.s10.5c4e1fac1bce from=translated src=- shape=19d84095 vocab=aa0e9b42
-/
theorem bracketLayer_map_subgroupImage_range_le (f : G →* H) (K : Subgroup G) [K.Normal]
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Submodule.map₂ (bracketLayer hi hj) ((subgroupImage K i).map (mapLayer f i))
      (LinearMap.range (mapLayer f j)) ≤ (subgroupImage K (i + j)).map (mapLayer f (i + j)) := by
  apply Submodule.map₂_le.mpr
  rintro x ⟨x, hx, rfl⟩ y ⟨y, rfl⟩
  rw [← mapLayer_bracketLayer]
  exact Submodule.mem_map.mpr ⟨_, bracketLayer_subgroupImage_top_le K hi hj
    (Submodule.apply_mem_map₂ _ hx Submodule.mem_top), rfl⟩

/-- Exchanging the arguments of the mixed bracket does not change its subspace image.

The two bracket maps differ by a minus sign; closure under negation removes that sign only
at the level of subspaces.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof lines 1011–1014.
@isnad1 id=eq.0h3v.s9.db3c4727e398 from=translated src=- shape=84c79c46 vocab=2d739140
-/
theorem map₂_bracketLayer_one_two (A : Submodule (ZMod 3) (Layer G 1))
    (B : Submodule (ZMod 3) (Layer G 2)) :
    Submodule.map₂ (bracketLayer (by decide) (by decide)) A B =
      Submodule.map₂ (bracketLayer (by decide) (by decide)) B A := by
  apply le_antisymm
  · apply Submodule.map₂_le.mpr
    intro x hx y hy
    rw [bracketLayer_one_two]
    exact Submodule.neg_mem _ (Submodule.apply_mem_map₂ _ hy hx)
  · apply Submodule.map₂_le.mpr
    intro y hy x hx
    rw [← neg_neg (bracketLayer (by decide) (by decide) y x), ← bracketLayer_one_two]
    exact Submodule.neg_mem _ (Submodule.apply_mem_map₂ _ hx hy)

end T3.AssociatedGraded

namespace T3.Coproduct.Presentation

open AssociatedGraded

variable {I J : Type*}

/-- The left free-factor retraction kills all generators of the right factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor identifications.-/
def freeProjectionLeft : Free (I ⊕ J) →* Free I :=
  liftFree Free.pow_three (MonoidHom.id _) 1

/-- The right free-factor retraction kills all generators of the left factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor identifications.-/
def freeProjectionRight : Free (I ⊕ J) →* Free J :=
  liftFree Free.pow_three 1 (MonoidHom.id _)

/-- The left projection is a retraction on the entire left free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor identifications.
@isnad1 id=eq.0h3v.s8.3417957a1a0c from=translated src=- shape=02e1bb45 vocab=bc9ae832
-/
@[simp]
theorem freeProjectionLeft_map_inl (x : Free I) :
    freeProjectionLeft (Free.map (Sum.inl : I → I ⊕ J) x) = x :=
  liftFree_map_inl Free.pow_three (MonoidHom.id _) 1 x

/-- The left projection kills the entire right free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor identifications.
@isnad1 id=eq.0h3v.s8.d6770c019a4f from=translated src=- shape=15ad03c6 vocab=711a6768
-/
@[simp]
theorem freeProjectionLeft_map_inr (x : Free J) :
    freeProjectionLeft (Free.map (Sum.inr : J → I ⊕ J) x) = 1 :=
  liftFree_map_inr Free.pow_three (MonoidHom.id _) 1 x

/-- The right projection kills the entire left free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor identifications.
@isnad1 id=eq.0h3v.s8.f685c45ed611 from=translated src=- shape=f3cedb2d vocab=550a5d61
-/
@[simp]
theorem freeProjectionRight_map_inl (x : Free I) :
    freeProjectionRight (Free.map (Sum.inl : I → I ⊕ J) x) = 1 :=
  liftFree_map_inl Free.pow_three 1 (MonoidHom.id _) x

/-- The right projection is a retraction on the entire right free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor identifications.
@isnad1 id=eq.0h3v.s8.52500f50f497 from=translated src=- shape=53259e1e vocab=461cb570
-/
@[simp]
theorem freeProjectionRight_map_inr (x : Free J) :
    freeProjectionRight (Free.map (Sum.inr : J → I ⊕ J) x) = x :=
  liftFree_map_inr Free.pow_three 1 (MonoidHom.id _) x

/-- The left projection and inclusion compose to the identity homomorphism.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor retraction.
@isnad1 id=eq.0h2v.s7.d3d96e5ad2c7 from=translated src=- shape=4bc695d1 vocab=aaaec7e8
-/
@[simp]
theorem freeProjectionLeft_comp_map_inl :
    (freeProjectionLeft (I := I) (J := J)).comp (Free.map Sum.inl) = MonoidHom.id _ := by
  ext x
  simp

/-- The right projection and inclusion compose to the identity homomorphism.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor retraction.
@isnad1 id=eq.0h2v.s7.6e509a8ee02c from=translated src=- shape=51cc89ce vocab=f6d40d38
-/
@[simp]
theorem freeProjectionRight_comp_map_inr :
    (freeProjectionRight (I := I) (J := J)).comp (Free.map Sum.inr) = MonoidHom.id _ := by
  ext x
  simp

/-- The left relation space is the transported ambient graded image computed in the left factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof lines 995–997.
@isnad1 id=eq.0h4v.s9.145e149de831 from=translated src=- shape=ac471a92 vocab=3c3730c9
-/
theorem subgroupImage_map_inl (K : Subgroup (Free I)) (n : ℕ) :
    subgroupImage (K.map (Free.map (Sum.inl : I → I ⊕ J))) n =
      (subgroupImage K n).map (mapLayer (Free.map Sum.inl) n) :=
  subgroupImage_map_of_leftInverse _ freeProjectionLeft freeProjectionLeft_comp_map_inl K n

/-- The right relation space is the transported ambient graded image computed in the right factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof lines 995–997.
@isnad1 id=eq.0h4v.s9.25ad774d5420 from=translated src=- shape=b333a4c4 vocab=d81f3d85
-/
theorem subgroupImage_map_inr (K : Subgroup (Free J)) (n : ℕ) :
    subgroupImage (K.map (Free.map (Sum.inr : J → I ⊕ J))) n =
      (subgroupImage K n).map (mapLayer (Free.map Sum.inr) n) :=
  subgroupImage_map_of_leftInverse _ freeProjectionRight freeProjectionRight_comp_map_inr K n

/-- Every first-degree vector is the sum of its two canonical factor projections.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, equality `V = V₀ ⊕ V₁`.
@isnad1 id=eq.0h3v.s12.977249018eed from=translated src=- shape=386a770f vocab=4d082234
-/
theorem mapLayer_inl_projection_add_inr_projection (x : Layer (Free (I ⊕ J)) 1) :
    mapLayer (Free.map Sum.inl) 1 (mapLayer freeProjectionLeft 1 x) +
      mapLayer (Free.map Sum.inr) 1 (mapLayer freeProjectionRight 1 x) = x := by
  let e : Layer (Free (I ⊕ J)) 1 →ₗ[ZMod 3] Layer (Free (I ⊕ J)) 1 :=
    (mapLayer (Free.map Sum.inl) 1).comp (mapLayer freeProjectionLeft 1) +
      (mapLayer (Free.map Sum.inr) 1).comp (mapLayer freeProjectionRight 1)
  let q : Free (I ⊕ J) →* MulLayer (Free (I ⊕ J)) 1 :=
    (QuotientGroup.mk' (relation (Free (I ⊕ J)) 1)).comp
      (Subgroup.topEquiv.symm.toMonoidHom)
  let h : MulLayer (Free (I ⊕ J)) 1 →* MulLayer (Free (I ⊕ J)) 1 :=
    MonoidHom.toAdditive.symm e.toAddMonoidHom
  have hh : h.comp q = q := by
    apply Free.hom_ext
    intro a
    apply Additive.ofMul.injective
    change e (mk _ 1 ⟨Free.of a, Subgroup.mem_top _⟩) =
      mk _ 1 ⟨Free.of a, Subgroup.mem_top _⟩
    cases a <;>
      simp [e, mapLayer_mk, termMap, freeProjectionLeft, freeProjectionRight, liftFree]
  obtain ⟨a, rfl⟩ := mk_surjective (Free (I ⊕ J)) 1 x
  exact congrArg Additive.ofMul (DFunLike.congr_fun hh (a : Free (I ⊕ J)))

/-- The two first-degree factor images exhaust the first layer of the combined free group.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, equality `V = V₀ ⊕ V₁`.
@isnad1 id=eq.0h2v.s11.b4f2d2482bbd from=translated src=- shape=59fcfee8 vocab=53377137
-/
theorem range_mapLayer_inl_sup_range_mapLayer_inr_one :
    LinearMap.range (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 1) ⊔
      LinearMap.range (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 1) = ⊤ := by
  apply top_unique
  intro x _
  rw [← mapLayer_inl_projection_add_inr_projection x]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
    (LinearMap.mem_range_self _ _)

variable (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J))

/-- The relation product's graded image is the sum of the two factor relation spaces,
transported by the canonical free inclusions.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof lines 995–1011.
@isnad1 id=eq.2h5v.s11.894ef047ca2f from=translated src=- shape=c2ded44b vocab=a6c46490
-/
theorem subgroupImage_relationSubgroup_eq_sup_map (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) (n : ℕ) :
    subgroupImage (relationSubgroup K₀ K₁) n =
      (subgroupImage K₀ n).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) n) ⊔
        (subgroupImage K₁ n).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) n) := by
  rw [subgroupImage_relationSubgroup K₀ K₁ h₀ h₁ n,
    subgroupImage_map_inl, subgroupImage_map_inr]

/-- The normal closure of the factor relations has zero first-degree image.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof line 975.
@isnad1 id=eq.2h4v.s9.ca8d056bb942 from=translated src=- shape=2e1f5d02 vocab=09ffdc5d
-/
theorem subgroupImage_relationKernel_one (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) : subgroupImage (relationKernel K₀ K₁) 1 = ⊥ :=
  subgroupImage_eq_bot_of_le 1 (relationKernel_le_commutator K₀ K₁ h₀ h₁)

/-- The second-degree relations of the normal closure are exactly the transported factor images.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof lines 975–1002.
@isnad1 id=eq.2h4v.s11.386d9103ca6b from=translated src=- shape=655bf75c vocab=6f19cd77
-/
theorem subgroupImage_relationKernel_two (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) :
    subgroupImage (relationKernel K₀ K₁) 2 =
      (subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2) ⊔
        (subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2) := by
  rw [relationKernel, subgroupImage_normalClosure_two
    (relationSubgroup_le_commutator K₀ K₁ h₀ h₁),
    subgroupImage_relationSubgroup_eq_sup_map K₀ K₁ h₀ h₁]

/-- The third-degree relations consist of the two factor images and brackets of the
second-degree relations with the full first layer of the combined free group.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof lines 1008–1011.
@isnad1 id=eq.2h4v.s12.3ad59f6564e0 from=translated src=- shape=e276e28e vocab=2d536d1d
-/
theorem subgroupImage_relationKernel_three (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) :
    subgroupImage (relationKernel K₀ K₁) 3 =
      ((subgroupImage K₀ 3).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 3) ⊔
        (subgroupImage K₁ 3).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 3)) ⊔
      Submodule.map₂ (bracketLayer (i := 2) (j := 1) (by decide) (by decide))
        ((subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2) ⊔
          (subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2)) ⊤ := by
  rw [relationKernel, subgroupImage_normalClosure_three
    (relationSubgroup_le_commutator K₀ K₁ h₀ h₁),
    subgroupImage_relationSubgroup_eq_sup_map K₀ K₁ h₀ h₁,
    subgroupImage_relationSubgroup_eq_sup_map K₀ K₁ h₀ h₁]

/-- Normal left-factor relations absorb their brackets with the left first-degree component.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, inclusion `R₀ ∧ V₀ ⊆ S₀`.
@isnad1 id=le.0h3v.s11.0b0aa899cc85 from=translated src=- shape=cb125882 vocab=eb9cb145
-/
theorem bracketLayer_inl_relation_le [K₀.Normal] :
    Submodule.map₂ (bracketLayer (i := 2) (j := 1) (by decide) (by decide))
      ((subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2))
      (LinearMap.range (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 1)) ≤
        (subgroupImage K₀ 3).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 3) :=
  bracketLayer_map_subgroupImage_range_le _ K₀ (by decide) (by decide)

/-- Normal right-factor relations absorb their brackets with the right first-degree component.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, inclusion `R₁ ∧ V₁ ⊆ S₁`.
@isnad1 id=le.0h3v.s11.f8905e043939 from=translated src=- shape=b7b98fbc vocab=8f72bd7b
-/
theorem bracketLayer_inr_relation_le [K₁.Normal] :
    Submodule.map₂ (bracketLayer (i := 2) (j := 1) (by decide) (by decide))
      ((subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2))
      (LinearMap.range (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 1)) ≤
        (subgroupImage K₁ 3).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 3) :=
  bracketLayer_map_subgroupImage_range_le _ K₁ (by decide) (by decide)

/-- After absorbing the same-factor brackets, the third-degree relation space consists of
the two pure relation spaces and the two mixed bracket spaces, in the paper's order.

The right mixed term is written with the left first-degree factor first. Its sign change is
valid because this is an equality of subspaces, not an equality of the two bracket maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, equality on line 1012.
@isnad1 id=eq.2h4v.s12.0d6e030f11d1 from=translated src=- shape=72f44364 vocab=3e38604b
-/
theorem subgroupImage_relationKernel_three_eq_four_blocks [K₀.Normal] [K₁.Normal]
    (h₀ : K₀ ≤ commutator (Free I)) (h₁ : K₁ ≤ commutator (Free J)) :
    subgroupImage (relationKernel K₀ K₁) 3 =
      (subgroupImage K₀ 3).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 3) ⊔
      Submodule.map₂ (bracketLayer (i := 2) (j := 1) (by decide) (by decide))
        ((subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2))
        (LinearMap.range (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 1)) ⊔
      Submodule.map₂ (bracketLayer (i := 1) (j := 2) (by decide) (by decide))
        (LinearMap.range (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 1))
        ((subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2)) ⊔
      (subgroupImage K₁ 3).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 3) := by
  let R₀ := (subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2)
  let R₁ := (subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2)
  let S₀ := (subgroupImage K₀ 3).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 3)
  let S₁ := (subgroupImage K₁ 3).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 3)
  let V₀ := LinearMap.range (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 1)
  let V₁ := LinearMap.range (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 1)
  let b := bracketLayer (G := Free (I ⊕ J)) (i := 2) (j := 1) (by decide) (by decide)
  rw [subgroupImage_relationKernel_three K₀ K₁ h₀ h₁, map₂_bracketLayer_one_two]
  change (S₀ ⊔ S₁) ⊔ Submodule.map₂ b (R₀ ⊔ R₁) ⊤ =
    S₀ ⊔ Submodule.map₂ b R₀ V₁ ⊔ Submodule.map₂ b R₁ V₀ ⊔ S₁
  rw [← range_mapLayer_inl_sup_range_mapLayer_inr_one (I := I) (J := J),
    Submodule.map₂_sup_left, Submodule.map₂_sup_right, Submodule.map₂_sup_right]
  calc
    _ = (S₀ ⊔ Submodule.map₂ b R₀ V₀) ⊔ Submodule.map₂ b R₀ V₁ ⊔
        Submodule.map₂ b R₁ V₀ ⊔ (S₁ ⊔ Submodule.map₂ b R₁ V₁) := by ac_rfl
    _ = _ := by
      rw [sup_eq_left.mpr (bracketLayer_inl_relation_le (J := J) K₀),
        sup_eq_left.mpr (bracketLayer_inr_relation_le (I := I) K₁)]

end T3.Coproduct.Presentation
