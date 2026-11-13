/-
# Monoids for Day convolution are lax monoidal functors

For monoidal categories `C` and `V`, the functors `C ⥤ V` with the Day convolution monoidal
structure form `C ⊛⥤ V` (Mathlib's `DayFunctor`), when `V` has the colimits defining Day
convolution and its tensor product preserves them. **A monoid for Day convolution is the same as a
lax monoidal functor** (Day): by the universal property of `F ⊗ F` as a left Kan extension, a
multiplication `F ⊗ F ⟶ F` is a natural family `F x ⊗ F y ⟶ F (x ⊗ y)`, and a unit
`𝟙 ⟶ F` is a map `𝟙_ V ⟶ F (𝟙_ C)`.

* `laxMonoidalOfMonObj` — the tensorator `μF` of a monoid is the unit of the Day convolution
  followed by the multiplication, and its unit `εF` is the unit of the Day unit followed by the
  unit of the monoid; the axioms of a lax monoidal functor are those of the monoid read on the
  units (`μF_assoc`, `μF_left_unitality`, `μF_right_unitality`).
* `monObjOfLaxMonoidal` — conversely the multiplication and the unit are induced by the
  tensorator and the unit (`mulL`, `oneL`); maps out of `(F ⊗ G) ⊗ H` are determined on the
  double units (`tensor₂_ext`), the tensor product of `V` preserving the colimits
  (`tensorRight_ext`).
* `monObjEquivLaxMonoidal` — **the two are inverse**, and **morphisms of monoids are the monoidal
  natural transformations** (`isMonHom_iff`).
* For `C` symmetric and `V` braided, **a monoid is commutative for the braiding of the Day
  convolution exactly when its tensorator commutes with the braidings** (`isCommDay_iff`): the
  commutative monoids are the lax braided (symmetric) functors (`laxBraidedOfCommDay`,
  `isCommDay_of_laxBraided`).
-/
import Tengoku.LeanOperads.Operad.DayUnits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace Operad

namespace DayMonoid

open scoped ExternalProduct CategoryTheory.Prod
open DayFunctor LawfulDayConvolutionMonoidalCategoryStruct

section Generic

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]

/--
@isnad1 id=eq.2h5v.s7.ef5df5ed8775 from=translated src=- shape=2f963566 vocab=1bc3cff5
-/
lemma laxMonoidal_ext {G : C ⥤ V} {L L' : G.LaxMonoidal}
    (hε : @Functor.LaxMonoidal.ε _ _ _ _ _ _ G L = @Functor.LaxMonoidal.ε _ _ _ _ _ _ G L')
    (hμ : ∀ x y, @Functor.LaxMonoidal.μ _ _ _ _ _ _ G L x y =
      @Functor.LaxMonoidal.μ _ _ _ _ _ _ G L' x y) : L = L' := by
  rcases L with ⟨ε, μ, _, _, _, _, _⟩
  rcases L' with ⟨ε', μ', _, _, _, _, _⟩
  obtain rfl : ε = ε' := hε
  obtain rfl : μ = μ' := funext fun x => funext fun y => hμ x y
  rfl

end Generic

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

section Forward

variable (F : C ⊛⥤ V) [MonObj F]

/-- **The tensorator of a Day monoid**.-/
noncomputable def μF (x y : C) : F.functor.obj x ⊗ F.functor.obj y ⟶ F.functor.obj (x ⊗ y) :=
  ηa F F x y ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y)

/-- **The unit of a Day monoid**.-/
noncomputable def εF : 𝟙_ V ⟶ F.functor.obj (𝟙_ C) :=
  ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ F).natTrans.app (𝟙_ C)

/--
@isnad1 id=eq.0h6v.s10.17577d81cacb from=translated src=- shape=97a44830 vocab=8731acbc
-/
@[reassoc]
lemma mul_naturality {a b : C} (f : a ⟶ b) :
    (F ⊗ F).functor.map f ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans.app b =
      (MonObj.mul : F ⊗ F ⟶ F).natTrans.app a ≫ F.functor.map f :=
  (MonObj.mul : F ⊗ F ⟶ F).natTrans.naturality f

/--
@isnad1 id=eq.0h7v.s9.04eaa598fba8 from=translated src=- shape=15dacbb6 vocab=08a0196b
-/
lemma μF_natural_left {x x' : C} (f : x ⟶ x') (y : C) :
    F.functor.map f ▷ F.functor.obj y ≫ μF F x' y = μF F x y ≫ F.functor.map (f ▷ y) := by
  simp only [μF, η_naturality_right_assoc, mul_naturality, Category.assoc]

/--
@isnad1 id=eq.0h7v.s9.82c2a140a7dc from=translated src=- shape=536caf5b vocab=0f6bf35e
-/
lemma μF_natural_right (x : C) {y y' : C} (g : y ⟶ y') :
    F.functor.obj x ◁ F.functor.map g ≫ μF F x y' = μF F x y ≫ F.functor.map (x ◁ g) := by
  simp only [μF, η_naturality_left_assoc, mul_naturality, Category.assoc]

/--
@isnad1 id=eq.0h6v.s10.72befef5ffb8 from=translated src=- shape=f1cfc782 vocab=b870f476
-/
lemma μF_assoc (x y z : C) :
    μF F x y ▷ F.functor.obj z ≫ μF F (x ⊗ y) z ≫ F.functor.map (α_ x y z).hom =
      (α_ _ _ _).hom ≫ F.functor.obj x ◁ μF F y z ≫ μF F x (y ⊗ z) := by
  have hassoc := congrArg (fun φ => φ.natTrans.app ((x ⊗ y) ⊗ z)) (MonObj.mul_assoc F)
  simp only [comp_natTrans, NatTrans.comp_app] at hassoc
  have hnat := (((F ◁ (MonObj.mul : F ⊗ F ⟶ F)) ≫ MonObj.mul).natTrans.naturality
    (α_ x y z).inv)
  simp only [comp_natTrans, NatTrans.comp_app] at hnat
  calc μF F x y ▷ F.functor.obj z ≫ μF F (x ⊗ y) z ≫ F.functor.map (α_ x y z).hom
      = ηa F F x y ▷ F.functor.obj z ≫ ηa (F ⊗ F) F (x ⊗ y) z ≫
          ((MonObj.mul : F ⊗ F ⟶ F) ▷ F).natTrans.app ((x ⊗ y) ⊗ z) ≫
          (MonObj.mul : F ⊗ F ⟶ F).natTrans.app ((x ⊗ y) ⊗ z) ≫
          F.functor.map (α_ x y z).hom := by
        rw [η_whiskerRight_assoc]
        simp only [μF, comp_whiskerRight, Category.assoc]
    _ = (α_ _ _ _).hom ≫ F.functor.obj x ◁ ηa F F y z ≫ ηa F (F ⊗ F) x (y ⊗ z) ≫
          (F ⊗ F ⊗ F).functor.map (α_ x y z).inv ≫
          (F ◁ (MonObj.mul : F ⊗ F ⟶ F)).natTrans.app ((x ⊗ y) ⊗ z) ≫
          (MonObj.mul : F ⊗ F ⟶ F).natTrans.app ((x ⊗ y) ⊗ z) ≫
          F.functor.map (α_ x y z).hom := by
        rw [reassoc_of% hassoc, η_associator_assoc]
    _ = (α_ _ _ _).hom ≫ F.functor.obj x ◁ ηa F F y z ≫ ηa F (F ⊗ F) x (y ⊗ z) ≫
          (F ◁ (MonObj.mul : F ⊗ F ⟶ F)).natTrans.app (x ⊗ y ⊗ z) ≫
          (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y ⊗ z) := by
        rw [reassoc_of% hnat]
        simp only [← F.functor.map_comp, Iso.inv_hom_id, F.functor.map_id, Category.comp_id]
    _ = _ := by
        rw [η_whiskerLeft_assoc]
        simp only [μF, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/--
@isnad1 id=eq.0h4v.s9.29724389b9bf from=translated src=- shape=50a04c43 vocab=15811825
-/
lemma μF_left_unitality (y : C) :
    (λ_ (F.functor.obj y)).hom = εF F ▷ F.functor.obj y ≫ μF F (𝟙_ C) y ≫
      F.functor.map (λ_ y).hom := by
  have hone := congrArg (fun φ => φ.natTrans.app (𝟙_ C ⊗ y)) (MonObj.one_mul F)
  simp only [comp_natTrans, NatTrans.comp_app] at hone
  calc (λ_ (F.functor.obj y)).hom =
      ((λ_ (F.functor.obj y)).hom ≫ F.functor.map (λ_ y).inv) ≫ F.functor.map (λ_ y).hom := by
        rw [Category.assoc, ← F.functor.map_comp, Iso.inv_hom_id, F.functor.map_id,
          Category.comp_id]
    _ = _ := by
        rw [← ν_leftUnitor, ← hone]
        simp only [εF, μF, comp_whiskerRight, Category.assoc, η_whiskerRight_assoc]

/--
@isnad1 id=eq.0h4v.s9.071f966afa84 from=translated src=- shape=31662e04 vocab=c04d5e90
-/
lemma μF_right_unitality (y : C) :
    (ρ_ (F.functor.obj y)).hom = F.functor.obj y ◁ εF F ≫ μF F y (𝟙_ C) ≫
      F.functor.map (ρ_ y).hom := by
  have hone := congrArg (fun φ => φ.natTrans.app (y ⊗ 𝟙_ C)) (MonObj.mul_one F)
  simp only [comp_natTrans, NatTrans.comp_app] at hone
  calc (ρ_ (F.functor.obj y)).hom =
      ((ρ_ (F.functor.obj y)).hom ≫ F.functor.map (ρ_ y).inv) ≫ F.functor.map (ρ_ y).hom := by
        rw [Category.assoc, ← F.functor.map_comp, Iso.inv_hom_id, F.functor.map_id,
          Category.comp_id]
    _ = _ := by
        rw [← ν_rightUnitor, ← hone]
        simp only [εF, μF, MonoidalCategory.whiskerLeft_comp, Category.assoc,
          η_whiskerLeft_assoc]

/-- **The lax monoidal functor of a monoid for Day convolution.**-/
@[implicit_reducible]
noncomputable def laxMonoidalOfMonObj : F.functor.LaxMonoidal where
  ε := εF F
  μ := μF F
  μ_natural_left f y := μF_natural_left F f y
  μ_natural_right x g := μF_natural_right F x g
  associativity x y z := μF_assoc F x y z
  left_unitality y := μF_left_unitality F y
  right_unitality y := μF_right_unitality F y

end Forward

section Backward

variable (F : C ⊛⥤ V) [F.functor.LaxMonoidal]

/-- The tensorator, as a natural transformation.-/
noncomputable def μNat : F.functor ⊠ F.functor ⟶ tensor C ⋙ F.functor where
  app p := Functor.LaxMonoidal.μ F.functor p.1 p.2
  naturality p q f := by
    simp [tensorHom_def]

/-- The multiplication of the lax monoidal functor.-/
noncomputable def mulL : F ⊗ F ⟶ F := tensorDesc (μNat F)

/-- The unit of the lax monoidal functor.-/
noncomputable def oneL : 𝟙_ (C ⊛⥤ V) ⟶ F := unitDesc (Functor.LaxMonoidal.ε F.functor)

/--
@isnad1 id=eq.0h5v.s9.918c6b2440fd from=translated src=- shape=feb4a53e vocab=74538ffb
-/
@[reassoc]
lemma ηa_mulL (x y : C) :
    ηa F F x y ≫ (mulL F).natTrans.app (x ⊗ y) = Functor.LaxMonoidal.μ F.functor x y :=
  ηa_tensorDesc _ x y

/--
@isnad1 id=eq.0h3v.s9.cddfd50bd51f from=translated src=- shape=3146b286 vocab=c62385ab
-/
@[reassoc]
lemma ν_oneL : ν C V ≫ (oneL F).natTrans.app (𝟙_ C) = Functor.LaxMonoidal.ε F.functor :=
  ν_comp_unitDesc _

/--
@isnad1 id=eq.0h3v.s10.068ece630761 from=translated src=- shape=b9c7aaba vocab=cffdd658
-/
lemma oneL_mul : oneL F ▷ F ≫ mulL F = (λ_ F).hom := by
  ext y
  simp only [comp_natTrans, NatTrans.comp_app]
  set s := (λ_ (F.functor.obj y)).inv ≫ ν C V ▷ F.functor.obj y ≫
    ηa (𝟙_ (C ⊛⥤ V)) F (𝟙_ C) y ≫ (𝟙_ (C ⊛⥤ V) ⊗ F).functor.map (λ_ y).hom with hsdef
  have hl : (λ_ F).hom.natTrans.app y ≫ (λ_ F).inv.natTrans.app y = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← comp_natTrans, Iso.hom_inv_id]
    rfl
  have hs : s ≫ (λ_ F).hom.natTrans.app y = 𝟙 _ := by
    rw [hsdef]
    simp only [Category.assoc]
    rw [(λ_ F).hom.natTrans.naturality (λ_ y).hom, ν_leftUnitor_assoc, ← F.functor.map_comp,
      Iso.inv_hom_id, F.functor.map_id, Category.comp_id, Iso.inv_hom_id]
  have hs' : s = (λ_ F).inv.natTrans.app y := by
    rw [← Category.comp_id s, ← hl, ← Category.assoc, hs, Category.id_comp]
  have hg : s ≫ (oneL F ▷ F).natTrans.app y ≫ (mulL F).natTrans.app y = 𝟙 _ := by
    have hnat := ((oneL F ▷ F) ≫ mulL F).natTrans.naturality (λ_ y).hom
    simp only [comp_natTrans, NatTrans.comp_app] at hnat
    rw [hsdef]
    simp only [Category.assoc]
    rw [hnat]
    simp only [Category.assoc]
    rw [η_whiskerRight_assoc, ηa_mulL_assoc, ← comp_whiskerRight_assoc, ν_oneL,
      ← Functor.LaxMonoidal.left_unitality, Iso.inv_hom_id]
  calc (oneL F ▷ F).natTrans.app y ≫ (mulL F).natTrans.app y
      = ((λ_ F).hom.natTrans.app y ≫ s) ≫ (oneL F ▷ F).natTrans.app y ≫
          (mulL F).natTrans.app y := by rw [hs', hl, Category.id_comp]
    _ = (λ_ F).hom.natTrans.app y := by rw [Category.assoc, hg, Category.comp_id]

/--
@isnad1 id=eq.0h3v.s10.82c2e548292f from=translated src=- shape=d4c353dc vocab=d732fc26
-/
lemma mul_oneL : F ◁ oneL F ≫ mulL F = (ρ_ F).hom := by
  ext y
  simp only [comp_natTrans, NatTrans.comp_app]
  set s := (ρ_ (F.functor.obj y)).inv ≫ F.functor.obj y ◁ ν C V ≫
    ηa F (𝟙_ (C ⊛⥤ V)) y (𝟙_ C) ≫ (F ⊗ 𝟙_ (C ⊛⥤ V)).functor.map (ρ_ y).hom with hsdef
  have hρ : (ρ_ F).hom.natTrans.app y ≫ (ρ_ F).inv.natTrans.app y = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← comp_natTrans, Iso.hom_inv_id]
    rfl
  have hs : s ≫ (ρ_ F).hom.natTrans.app y = 𝟙 _ := by
    rw [hsdef]
    simp only [Category.assoc]
    rw [(ρ_ F).hom.natTrans.naturality (ρ_ y).hom, ν_rightUnitor_assoc, ← F.functor.map_comp,
      Iso.inv_hom_id, F.functor.map_id, Category.comp_id, Iso.inv_hom_id]
  have hs' : s = (ρ_ F).inv.natTrans.app y := by
    rw [← Category.comp_id s, ← hρ, ← Category.assoc, hs, Category.id_comp]
  have hg : s ≫ (F ◁ oneL F).natTrans.app y ≫ (mulL F).natTrans.app y = 𝟙 _ := by
    have hnat := ((F ◁ oneL F) ≫ mulL F).natTrans.naturality (ρ_ y).hom
    simp only [comp_natTrans, NatTrans.comp_app] at hnat
    rw [hsdef]
    simp only [Category.assoc]
    rw [hnat]
    simp only [Category.assoc]
    rw [η_whiskerLeft_assoc, ηa_mulL_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ν_oneL, ← Functor.LaxMonoidal.right_unitality, Iso.inv_hom_id]
  calc (F ◁ oneL F).natTrans.app y ≫ (mulL F).natTrans.app y
      = ((ρ_ F).hom.natTrans.app y ≫ s) ≫ (F ◁ oneL F).natTrans.app y ≫
          (mulL F).natTrans.app y := by rw [hs', hρ, Category.id_comp]
    _ = (ρ_ F).hom.natTrans.app y := by rw [Category.assoc, hg, Category.comp_id]

end Backward

/-! ## The dictionary -/

/--
@isnad1 id=eq.2h5v.s9.9c81fc825ad3 from=translated src=- shape=db7cd458 vocab=6fa548f0
-/
lemma monObj_ext {F : C ⊛⥤ V} {M M' : MonObj F}
    (hone : @MonObj.one _ _ _ F M = @MonObj.one _ _ _ F M')
    (hmul : @MonObj.mul _ _ _ F M = @MonObj.mul _ _ _ F M') : M = M' := by
  rcases M with ⟨one, mul, _, _, _⟩
  rcases M' with ⟨one', mul', _, _, _⟩
  obtain rfl : one = one' := hone
  obtain rfl : mul = mul' := hmul
  rfl

/-- **Morphisms of monoids are monoidal natural transformations.**
@isnad1 id=iff.0h5v.s9.d3d68562aa13 from=translated src=- shape=0018b113 vocab=b1a91909
-/
theorem isMonHom_iff {M N : C ⊛⥤ V} [MonObj M] [MonObj N] (f : M ⟶ N) :
    IsMonHom f ↔ @NatTrans.IsMonoidal _ _ _ _ _ _ M.functor N.functor f.natTrans
      (laxMonoidalOfMonObj M) (laxMonoidalOfMonObj N) := by
  letI := laxMonoidalOfMonObj M
  letI := laxMonoidalOfMonObj N
  constructor
  · intro hf
    refine ⟨?_, fun x y => ?_⟩
    · show (ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ M).natTrans.app (𝟙_ C)) ≫
          f.natTrans.app (𝟙_ C) = ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ N).natTrans.app (𝟙_ C)
      rw [Category.assoc, ← NatTrans.comp_app, ← comp_natTrans, IsMonHom.one_hom]
    · show (ηa M M x y ≫ (MonObj.mul : M ⊗ M ⟶ M).natTrans.app (x ⊗ y)) ≫
          f.natTrans.app (x ⊗ y) = (f.natTrans.app x ⊗ₘ f.natTrans.app y) ≫
          ηa N N x y ≫ (MonObj.mul : N ⊗ N ⟶ N).natTrans.app (x ⊗ y)
      rw [Category.assoc, ← NatTrans.comp_app, ← comp_natTrans, IsMonHom.mul_hom,
        comp_natTrans, NatTrans.comp_app, η_tensorHom_assoc]
  · intro hf
    refine ⟨?_, ?_⟩
    · refine unit_hom_ext ?_
      have h := hf.unit
      change (ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ M).natTrans.app (𝟙_ C)) ≫
          f.natTrans.app (𝟙_ C) = ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ N).natTrans.app (𝟙_ C) at h
      simpa only [comp_natTrans, NatTrans.comp_app, Category.assoc] using h
    · refine tensor_ext fun x y => ?_
      have h := hf.tensor x y
      change (ηa M M x y ≫ (MonObj.mul : M ⊗ M ⟶ M).natTrans.app (x ⊗ y)) ≫
          f.natTrans.app (x ⊗ y) = (f.natTrans.app x ⊗ₘ f.natTrans.app y) ≫
          ηa N N x y ≫ (MonObj.mul : N ⊗ N ⟶ N).natTrans.app (x ⊗ y) at h
      simp only [comp_natTrans, NatTrans.comp_app, Category.assoc] at h ⊢
      rw [h, η_tensorHom_assoc]

/-! ## Commutative monoids and lax braided functors -/

section Braided

variable [SymmetricCategory C] [BraidedCategory V]

/-- The Day convolution of the underlying functors.-/
noncomputable abbrev dayConv (F G : C ⊛⥤ V) : DayConvolution F.functor G.functor :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (C ⊛⥤ V) F G

/-- **The braiding of the Day convolution** of `F` with itself.-/
noncomputable def dayBraiding (F : C ⊛⥤ V) : (F ⊗ F).functor ≅ (F ⊗ F).functor :=
  @DayConvolution.braiding C _ V _ _ _ _ _ F.functor F.functor (dayConv F F) (dayConv F F)

/--
@isnad1 id=eq.0h5v.s10.08d846757f2b from=translated src=- shape=32c7e215 vocab=1f300754
-/
@[reassoc]
lemma ηa_dayBraiding (F : C ⊛⥤ V) (x y : C) :
    ηa F F x y ≫ (dayBraiding F).hom.app (x ⊗ y) =
      (β_ _ _).hom ≫ ηa F F y x ≫ (F ⊗ F).functor.map (β_ y x).hom :=
  @DayConvolution.unit_app_braiding_hom_app C _ V _ _ _ _ _ F.functor F.functor
    (dayConv F F) (dayConv F F) x y

/-- **A commutative monoid for Day convolution**: the multiplication is invariant under the
braiding.-/
def IsCommDay (F : C ⊛⥤ V) [MonObj F] : Prop :=
  (dayBraiding F).hom ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans = (MonObj.mul : F ⊗ F ⟶ F).natTrans

/--
@isnad1 id=eq.0h5v.s10.041e4b058e3d from=translated src=- shape=c16c20b0 vocab=25b02159
-/
lemma ηa_dayBraiding_mul (F : C ⊛⥤ V) [MonObj F] (x y : C) :
    ηa F F x y ≫ (dayBraiding F).hom.app (x ⊗ y) ≫
        (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y) =
      (β_ _ _).hom ≫ μF F y x ≫ F.functor.map (β_ y x).hom := by
  rw [ηa_dayBraiding_assoc, mul_naturality, μF]
  simp only [Category.assoc]

/-- **Commutative monoids for Day convolution are lax braided functors**: the multiplication is
commutative exactly when the tensorator commutes with the braidings.
@isnad1 id=iff.0h3v.s10.37e3733226c9 from=translated src=- shape=a044269e vocab=85d33116
-/
theorem isCommDay_iff (F : C ⊛⥤ V) [MonObj F] :
    IsCommDay F ↔ ∀ x y : C,
      μF F x y ≫ F.functor.map (β_ x y).hom = (β_ _ _).hom ≫ μF F y x := by
  constructor
  · intro h x y
    have hxy := congrArg (fun φ => ηa F F x y ≫ φ.app (x ⊗ y)) h
    simp only [NatTrans.comp_app] at hxy
    rw [ηa_dayBraiding_mul] at hxy
    rw [← show ηa F F x y ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y) = μF F x y from rfl,
      ← hxy]
    simp only [Category.assoc, ← F.functor.map_comp, SymmetricCategory.symmetry,
      F.functor.map_id, Category.comp_id]
  · intro h
    have key : (DayFunctor.Hom.mk ((dayBraiding F).hom ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans) :
        F ⊗ F ⟶ F) = (MonObj.mul : F ⊗ F ⟶ F) := by
      refine tensor_ext fun x y => ?_
      show ηa F F x y ≫ ((dayBraiding F).hom ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans).app (x ⊗ y) =
        _
      rw [NatTrans.comp_app, ηa_dayBraiding_mul, ← Category.assoc, ← h x y, Category.assoc,
        ← F.functor.map_comp, SymmetricCategory.symmetry, F.functor.map_id, Category.comp_id]
      rfl
    exact congrArg DayFunctor.Hom.natTrans key

/-- **The lax braided functor of a commutative monoid for Day convolution.**-/
@[implicit_reducible]
noncomputable def laxBraidedOfCommDay (F : C ⊛⥤ V) [MonObj F] (h : IsCommDay F) :
    F.functor.LaxBraided where
  toLaxMonoidal := laxMonoidalOfMonObj F
  braided x y := (isCommDay_iff F).1 h x y

end Braided

end DayMonoid

end Operad
