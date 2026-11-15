import Tengoku.Seed.AlgebraicGeometry.Sites.ConstantSheaf
import Tengoku.Seed.AlgebraicGeometry.AffineSpace
import Tengoku.Seed.AlgebraicGeometry.Limits
import Tengoku.Seed.CategoryTheory.Sites.SubcanonicalOver
import Tengoku.Seed.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Tengoku.Seed.Algebra.Category.Grp.Adjunctions
import Tengoku.Seed.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace FppfRepresentableGroupSchemeSheaf

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe w v₁ u₁ u

section TypeValued

/--
@isnad1 id=issheaf.0h1v.s4.1eba2240ff96 from=translated src=- shape=ff636396 vocab=fef43a06
-/
theorem isSheaf_fppf_of_isRepresentable (P : Scheme.{u}ᵒᵖ ⥤ Type u) [P.IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology P := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

/--
@isnad1 id=issheaf.0h1v.s4.80e8ed060392 from=translated src=- shape=ff636396 vocab=e47e8039
-/
theorem isSheaf_fpqc_of_isRepresentable (P : Scheme.{u}ᵒᵖ ⥤ Type u) [P.IsRepresentable] :
    Presheaf.IsSheaf Scheme.fpqcTopology P := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

/--
@isnad1 id=issheaf.0h1v.s4.a02581fc3044 from=translated src=- shape=1c1e16f7 vocab=d7b9181c
-/
theorem isSheaf_fppf_yoneda (G : Scheme.{u}) :
    Presheaf.IsSheaf Scheme.fppfTopology (yoneda.obj G) :=
  isSheaf_fppf_of_isRepresentable _

/--
@isnad1 id=issheaf.0h3v.s4.a62b6a651a5e from=translated src=- shape=ae4d3475 vocab=ecd06fbd
-/
theorem isSheaf_fppf_of_representableBy (P : Scheme.{u}ᵒᵖ ⥤ Type u) {G : Scheme.{u}}
    (h : P.RepresentableBy G) :
    Presheaf.IsSheaf Scheme.fppfTopology P :=
  have : P.IsRepresentable := h.isRepresentable
  isSheaf_fppf_of_isRepresentable P

/--
@isnad1 id=issheaf.0h1v.s4.83ded0b8d3bd from=translated src=- shape=749928ba vocab=fcaaf994
-/
theorem presieve_isSheaf_fppf_of_isRepresentable (P : Scheme.{u}ᵒᵖ ⥤ Type u)
    [P.IsRepresentable] : Presieve.IsSheaf Scheme.fppfTopology P :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

end TypeValued

section StructuredValues

/--
@isnad1 id=issheaf.0h1v.s6.d63933f43f13 from=translated src=- shape=2e06399c vocab=3e84a55e
-/
theorem isSheaf_fppf_monCat_of_forget_isRepresentable (F : Scheme.{u}ᵒᵖ ⥤ MonCat.{u})
    [(F ⋙ forget MonCat).IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology F :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget MonCat)
    (isSheaf_fppf_of_isRepresentable (F ⋙ forget MonCat))

/--
@isnad1 id=issheaf.0h1v.s6.697e9dccce71 from=translated src=- shape=2e06399c vocab=85d2ed06
-/
theorem isSheaf_fppf_grpCat_of_forget_isRepresentable (F : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u})
    [(F ⋙ forget GrpCat).IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology F :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget GrpCat)
    (isSheaf_fppf_of_isRepresentable (F ⋙ forget GrpCat))

/--
@isnad1 id=issheaf.0h1v.s6.28d288a3992b from=translated src=- shape=2e06399c vocab=d9067d98
-/
theorem isSheaf_fppf_commGrpCat_of_forget_isRepresentable (F : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u})
    [(F ⋙ forget CommGrpCat).IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology F :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget CommGrpCat)
    (isSheaf_fppf_of_isRepresentable (F ⋙ forget CommGrpCat))

/--
@isnad1 id=issheaf.0h1v.s6.516b4f7158ac from=translated src=- shape=2e06399c vocab=2c80a488
-/
theorem isSheaf_fppf_ab_of_forget_isRepresentable (F : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u})
    [(F ⋙ forget AddCommGrpCat).IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology F :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat)
    (isSheaf_fppf_of_isRepresentable (F ⋙ forget AddCommGrpCat))

end StructuredValues

section GroupSchemeOverZ

variable (G : Scheme.{u}) [GrpObj G]

/--
@isnad1 id=issheaf.0h1v.s4.22c124faea8b from=translated src=- shape=952ad3c7 vocab=291e335d
-/
theorem isSheaf_fppf_yonedaGrpObj :
    Presheaf.IsSheaf Scheme.fppfTopology (yonedaGrpObj G) :=
  have : (yonedaGrpObj G ⋙ forget GrpCat).IsRepresentable :=
    (yonedaGrpObjRepresentableBy G).isRepresentable
  isSheaf_fppf_grpCat_of_forget_isRepresentable _

def fppfGrpSheaf : Sheaf Scheme.fppfTopology GrpCat.{u} :=
  ⟨yonedaGrpObj G, isSheaf_fppf_yonedaGrpObj G⟩

variable [IsCommMonObj G]

def yonedaCommGrpObj : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (unop T ⟶ G)
  map φ := CommGrpCat.ofHom ((yonedaGrpObj G).map φ).hom
  map_id _ := CommGrpCat.hom_ext (MonoidHom.ext fun g => Category.id_comp g)
  map_comp φ ψ := CommGrpCat.hom_ext (MonoidHom.ext fun g => Category.assoc ψ.unop φ.unop g)

def yonedaCommGrpObjRepresentableBy :
    (yonedaCommGrpObj G ⋙ forget CommGrpCat).RepresentableBy G where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/--
@isnad1 id=issheaf.0h1v.s5.ebbd73677c0f from=translated src=- shape=c66d3311 vocab=a4a709c8
-/
theorem isSheaf_fppf_yonedaCommGrpObj :
    Presheaf.IsSheaf Scheme.fppfTopology (yonedaCommGrpObj G) :=
  have : (yonedaCommGrpObj G ⋙ forget CommGrpCat).IsRepresentable :=
    (yonedaCommGrpObjRepresentableBy G).isRepresentable
  isSheaf_fppf_commGrpCat_of_forget_isRepresentable _

def fppfCommGrpSheaf : Sheaf Scheme.fppfTopology CommGrpCat.{u} :=
  ⟨yonedaCommGrpObj G, isSheaf_fppf_yonedaCommGrpObj G⟩

def yonedaAddCommGrpObj : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yonedaCommGrpObj G ⋙ commGroupAddCommGroupEquivalence.functor

/--
@isnad1 id=issheaf.0h1v.s5.244f179bef1f from=translated src=- shape=c66d3311 vocab=08f8dc40
-/
theorem isSheaf_fppf_yonedaAddCommGrpObj :
    Presheaf.IsSheaf Scheme.fppfTopology (yonedaAddCommGrpObj G) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ commGroupAddCommGroupEquivalence.functor
    (isSheaf_fppf_yonedaCommGrpObj G)

def fppfAbelianSheaf : Sheaf Scheme.fppfTopology AddCommGrpCat.{u} :=
  ⟨yonedaAddCommGrpObj G, isSheaf_fppf_yonedaAddCommGrpObj G⟩

end GroupSchemeOverZ

section SectionsIdentification

variable (G : Scheme.{u}) [GrpObj G]

def fppfGrpSheafSectionsMulEquiv (T : Scheme.{u}) :
    ((fppfGrpSheaf G).obj.obj (op T)) ≃* (T ⟶ G) :=
  MulEquiv.refl _

variable [IsCommMonObj G]

def fppfCommGrpSheafSectionsMulEquiv (T : Scheme.{u}) :
    ((fppfCommGrpSheaf G).obj.obj (op T)) ≃* (T ⟶ G) :=
  MulEquiv.refl _

def fppfAbelianSheafSectionsAddEquiv (T : Scheme.{u}) :
    ((fppfAbelianSheaf G).obj.obj (op T)) ≃+ Additive (T ⟶ G) :=
  AddEquiv.refl _

def fppfAbelianSheafGlobalSectionsAddEquiv :
    ((fppfAbelianSheaf G).obj.obj (op (𝟙_ Scheme.{u}))) ≃+ Additive (𝟙_ Scheme.{u} ⟶ G) :=
  fppfAbelianSheafSectionsAddEquiv G (𝟙_ Scheme.{u})

end SectionsIdentification

section GroupSchemeOverBase

variable (S : Scheme.{u})

abbrev fppfTopologyOver : GrothendieckTopology (Over S) :=
  Scheme.fppfTopology.over S

variable (G : Over S) [GrpObj G]

/--
@isnad1 id=issheaf.0h2v.s5.fe8f137dd5bf from=translated src=- shape=f4225f3f vocab=f229a2c5
-/
theorem isSheaf_fppfOver_yonedaGrpObj :
    Presheaf.IsSheaf (fppfTopologyOver S) (yonedaGrpObj G) :=
  have : (yonedaGrpObj G ⋙ forget GrpCat).IsRepresentable :=
    (yonedaGrpObjRepresentableBy G).isRepresentable
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget GrpCat) (by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

def fppfOverGrpSheaf : Sheaf (fppfTopologyOver S) GrpCat.{u} :=
  ⟨yonedaGrpObj G, isSheaf_fppfOver_yonedaGrpObj S G⟩

variable [IsCommMonObj G]

def yonedaCommGrpObjOver : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (unop T ⟶ G)
  map φ := CommGrpCat.ofHom ((yonedaGrpObj G).map φ).hom
  map_id _ := CommGrpCat.hom_ext (MonoidHom.ext fun g => Category.id_comp g)
  map_comp φ ψ := CommGrpCat.hom_ext (MonoidHom.ext fun g => Category.assoc ψ.unop φ.unop g)

def yonedaCommGrpObjOverRepresentableBy :
    (yonedaCommGrpObjOver S G ⋙ forget CommGrpCat).RepresentableBy G where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/--
@isnad1 id=issheaf.0h2v.s6.b375b04dd821 from=translated src=- shape=ce9fd314 vocab=23107cda
-/
theorem isSheaf_fppfOver_yonedaCommGrpObjOver :
    Presheaf.IsSheaf (fppfTopologyOver S) (yonedaCommGrpObjOver S G) :=
  have : (yonedaCommGrpObjOver S G ⋙ forget CommGrpCat).IsRepresentable :=
    (yonedaCommGrpObjOverRepresentableBy S G).isRepresentable
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget CommGrpCat) (by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

def yonedaAddCommGrpObjOver : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yonedaCommGrpObjOver S G ⋙ commGroupAddCommGroupEquivalence.functor

/--
@isnad1 id=issheaf.0h2v.s6.e9f66d7b7d5c from=translated src=- shape=ce9fd314 vocab=e1e34d60
-/
theorem isSheaf_fppfOver_yonedaAddCommGrpObjOver :
    Presheaf.IsSheaf (fppfTopologyOver S) (yonedaAddCommGrpObjOver S G) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ commGroupAddCommGroupEquivalence.functor
    (isSheaf_fppfOver_yonedaCommGrpObjOver S G)

def fppfOverAbelianSheaf : Sheaf (fppfTopologyOver S) AddCommGrpCat.{u} :=
  ⟨yonedaAddCommGrpObjOver S G, isSheaf_fppfOver_yonedaAddCommGrpObjOver S G⟩

def fppfOverAbelianSheafSectionsAddEquiv (T : Over S) :
    ((fppfOverAbelianSheaf S G).obj.obj (op T)) ≃+ Additive (T ⟶ G) :=
  AddEquiv.refl _

end GroupSchemeOverBase

section UnitsDescent

variable {C : Type u₁} [Category.{v₁} C]

def unitsPresheaf (O : Cᵒᵖ ⥤ CommRingCat.{w}) : Cᵒᵖ ⥤ CommGrpCat.{w} :=
  O ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

/--
@isnad1 id=issheaf.1h3v.s7.bbf39ae2b1a5 from=translated src=- shape=44c2e491 vocab=14cfbbb3
-/
theorem presieve_isSheaf_units {J : GrothendieckTopology C} {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (hO : Presieve.IsSheaf J (O ⋙ forget CommRingCat)) :
    Presieve.IsSheaf J (unitsPresheaf O ⋙ forget CommGrpCat) := by
  intro X S hS x hx

  let xu : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S.arrows f → ((O.obj (op Y)) : Type w)ˣ := fun _ f hf => x f hf

  let v : Presieve.FamilyOfElements (O ⋙ forget CommRingCat) S.arrows :=
    fun Y f hf => ((xu f hf : ((O.obj (op Y)) : Type w)ˣ) : (O.obj (op Y)))
  let w' : Presieve.FamilyOfElements (O ⋙ forget CommRingCat) S.arrows :=
    fun Y f hf => (((xu f hf)⁻¹ : ((O.obj (op Y)) : Type w)ˣ) : (O.obj (op Y)))

  have hv : v.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact congrArg Units.val (hx g₁ g₂ h₁ h₂ hcomm)
  have hw : w'.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact congrArg (fun u : ((O.obj (op Z)) : Type w)ˣ => ((u⁻¹ : _ˣ) : (O.obj (op Z))))
      (hx g₁ g₂ h₁ h₂ hcomm)

  obtain ⟨a, ha, ha_uniq⟩ := hO S hS v hv
  obtain ⟨b, hb, -⟩ := hO S hS w' hw

  have hab : a * b = 1 := by
    apply (hO S hS).isSeparatedFor.ext
    intro Y f hf
    have h1 : (O.map f.op).hom (a * b) =
        (O.map f.op).hom a * (O.map f.op).hom b := map_mul _ a b
    have h2 : (O.map f.op).hom (1 : (O.obj (op X))) = 1 := map_one _
    have ha' : (O.map f.op).hom a = v f hf := ha f hf
    have hb' : (O.map f.op).hom b = w' f hf := hb f hf
    show (O.map f.op).hom (a * b) = (O.map f.op).hom (1 : (O.obj (op X)))
    rw [h1, h2, ha', hb']
    exact Units.mul_inv _
  have hba : b * a = 1 := by rw [mul_comm]; exact hab

  refine ⟨(⟨a, b, hab, hba⟩ : ((O.obj (op X)) : Type w)ˣ), ?_, ?_⟩
  ·
    intro Y f hf
    show Units.map (O.map f.op).hom.toMonoidHom (⟨a, b, hab, hba⟩ : ((O.obj (op X)) : Type w)ˣ)
      = xu f hf
    apply Units.ext
    show (O.map f.op).hom a = ((xu f hf : ((O.obj (op Y)) : Type w)ˣ) : (O.obj (op Y)))
    exact ha f hf
  ·
    intro u hu

    let u' : ((O.obj (op X)) : Type w)ˣ := u
    have hval : (u' : (O.obj (op X))) = a := by
      apply ha_uniq
      intro Y f hf
      exact congrArg Units.val (hu f hf)
    show u' = (⟨a, b, hab, hba⟩ : ((O.obj (op X)) : Type w)ˣ)
    exact Units.ext hval

end UnitsDescent

section Instances

abbrev affineLineOverZ : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))

def gammaRepresentableBy :
    (Scheme.Γ.{u} ⋙ forget CommRingCat).RepresentableBy affineLineOverZ.{u} where
  homEquiv {X} := (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} (X := X)).trans
    (Equiv.funUnique PUnit.{u + 1} _)
  homEquiv_comp f g := by
    show AffineSpace.toSpecMvPolyIntEquiv _ (f ≫ g) PUnit.unit = _
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp]
    rfl

/--
@isnad1 id=issheaf.0h0v.s6.22a84e905d16 from=translated src=- shape=59d48f54 vocab=80fe2eda
-/
theorem presieve_isSheaf_fppf_gammaForget :
    Presieve.IsSheaf Scheme.fppfTopology.{u} (Scheme.Γ ⋙ forget CommRingCat) :=
  have : (Scheme.Γ.{u} ⋙ forget CommRingCat).IsRepresentable :=
    gammaRepresentableBy.{u}.isRepresentable
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

def Gm : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u} :=
  unitsPresheaf Scheme.Γ

/--
@isnad1 id=issheaf.0h0v.s2.1f80314f602d from=translated src=- shape=93eefbde vocab=b16d5a3a
-/
theorem isSheaf_fppf_Gm : Presheaf.IsSheaf Scheme.fppfTopology.{u} Gm.{u} := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget CommGrpCat)
  rw [isSheaf_iff_isSheaf_of_type]
  exact presieve_isSheaf_units presieve_isSheaf_fppf_gammaForget

def GmSheaf : Sheaf Scheme.fppfTopology.{u} CommGrpCat.{u} :=
  ⟨Gm, isSheaf_fppf_Gm⟩

def GmSectionsMulEquiv (X : Scheme.{u}) :
    ((Gm.{u}).obj (op X) : Type u) ≃* ((Γ(X, ⊤) : Type u))ˣ :=
  MulEquiv.refl _

def GmAbelianSheaf : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u} :=
  ⟨Gm ⋙ commGroupAddCommGroupEquivalence.functor,
    Presheaf.isSheaf_comp_of_isSheaf _ _ commGroupAddCommGroupEquivalence.functor
      isSheaf_fppf_Gm⟩

def mu (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type u :=
  Gm ⋙ coyoneda.obj (op (CommGrpCat.of (ULift.{u} (Multiplicative (ZMod n)))))

/--
@isnad1 id=issheaf.0h1v.s3.95389ca760ca from=translated src=- shape=7000f90d vocab=26d1fbb1
-/
theorem presieve_isSheaf_fppf_mu (n : ℕ) :
    Presieve.IsSheaf Scheme.fppfTopology.{u} (mu.{u} n) :=
  isSheaf_fppf_Gm (CommGrpCat.of (ULift.{u} (Multiplicative (ZMod n))))

/--
@isnad1 id=eq.0h2v.s5.4adef019d6bf from=translated src=- shape=bb302e55 vocab=08493523
-/
theorem mu_obj (n : ℕ) (X : Scheme.{u}) :
    (mu.{u} n).obj (op X) =
      (CommGrpCat.of (ULift.{u} (Multiplicative (ZMod n))) ⟶ Gm.{u}.obj (op X)) :=
  rfl

section ConstantZMod

variable (n : ℕ)

local instance : TopologicalSpace (ZMod n) := ⊥

local instance : DiscreteTopology (ZMod n) := ⟨rfl⟩

local instance : IsTopologicalAddGroup (ZMod n) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def constantZMod : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  continuousMapPresheafAb (ZMod n)

/--
@isnad1 id=issheaf.0h1v.s3.445aba73dba2 from=translated src=- shape=74806ba1 vocab=276eb6f4
-/
theorem isSheaf_fppf_constantZMod :
    Presheaf.IsSheaf Scheme.fppfTopology.{u} (constantZMod.{u} n) :=
  Presheaf.IsSheaf.of_le Scheme.fppfTopology_le_fpqcTopology
    (isSheaf_fpqcTopology_continuousMapPresheafAb (ZMod n))

def constantZModSheaf : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u} :=
  ⟨constantZMod n, isSheaf_fppf_constantZMod n⟩

end ConstantZMod

end Instances

section Gates

instance : IsCommMonObj (𝟙_ Scheme.{u}) where
  mul_comm := isTerminalTensorUnit.hom_ext _ _

def gateTrivialGroupSchemeAbelianSheaf : Sheaf Scheme.fppfTopology AddCommGrpCat.{u} :=
  fppfAbelianSheaf (𝟙_ Scheme.{u})

/--
@isnad1 id=subsingl.0h1v.s5.765cc0fbe501 from=translated src=- shape=58930d81 vocab=e9a7734c
-/
instance gateTrivialSheafSectionsSubsingleton (T : Scheme.{u}) :
    Subsingleton ((gateTrivialGroupSchemeAbelianSheaf.{u}).obj.obj (op T)) :=
  ⟨fun a b => by
    have h : ∀ x y : Additive (T ⟶ 𝟙_ Scheme.{u}), x = y := fun x y =>
      congrArg Additive.ofMul (isTerminalTensorUnit.hom_ext x.toMul y.toMul)
    exact (fppfAbelianSheafSectionsAddEquiv (𝟙_ Scheme.{u}) T).injective (h _ _)⟩

/--
@isnad1 id=mem.0h3v.s6.1347115dd787 from=translated src=- shape=8b70bf36 vocab=5b35b473
-/
theorem gate_singleton_generates_fppf_cover {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [Surjective f] [LocallyOfFinitePresentation f] :
    Sieve.generate (Presieve.singleton f) ∈ Scheme.fppfTopology Y :=
  Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage f)

def gateGmSectionsSpecZ :
    ((Gm.{0}).obj (op (Spec (CommRingCat.of ℤ))) : Type 0) ≃* ℤˣ :=
  (GmSectionsMulEquiv (Spec (CommRingCat.of ℤ))).trans
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.toMulEquiv)

/--
@isnad1 id=nontrivi.0h0v.s4.87c941b12fc8 from=translated src=- shape=02a6975d vocab=66bb8919
-/
theorem gate_Gm_sections_nontrivial :
    Nontrivial ((Gm.{0}).obj (op (Spec (CommRingCat.of ℤ))) : Type 0) :=
  haveI : Nontrivial ℤˣ := ⟨1, -1, by decide⟩
  gateGmSectionsSpecZ.toEquiv.nontrivial

end Gates

end FppfRepresentableGroupSchemeSheaf
