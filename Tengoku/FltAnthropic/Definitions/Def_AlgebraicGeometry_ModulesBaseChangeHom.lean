import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf
import Tengoku.Seed.CategoryTheory.Adjunction.Mates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}

def pullbackTwoSquare (h : g' ≫ π = π' ≫ ψ) :
    TwoSquare (pullback ψ) (pullback π) (pullback π') (pullback g') :=
  (pullbackComp π' ψ).hom ≫ (pullbackCongr h.symm).hom ≫ (pullbackComp g' π).inv

def baseChangeNatTrans (h : g' ≫ π = π' ≫ ψ) :
    TwoSquare (pushforward π) (pullback g') (pullback ψ) (pushforward π') :=
  mateEquiv (pullbackPushforwardAdjunction π) (pullbackPushforwardAdjunction π') (pullbackTwoSquare h)

def baseChangeHom (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullback ψ).obj ((pushforward π).obj F) ⟶ (pushforward π').obj ((pullback g').obj F) :=
  (baseChangeNatTrans h).natTrans.app F

/--
@isnad1 id=eq.1h9v.s8.f59c5929fc88 from=translated src=- shape=fe4061ee vocab=b10559f0
-/
theorem baseChangeNatTrans_app (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (baseChangeNatTrans h).natTrans.app F = baseChangeHom h F := rfl

/--
@isnad1 id=eq.1h11v.s8.d658f93d452f from=translated src=- shape=54f7c1bb vocab=351959c5
-/
theorem baseChangeHom_naturality (h : g' ≫ π = π' ≫ ψ) {F G : X.Modules} (φ : F ⟶ G) :
    (pullback ψ).map ((pushforward π).map φ) ≫ baseChangeHom h G =
      baseChangeHom h F ≫ (pushforward π').map ((pullback g').map φ) :=
  (baseChangeNatTrans h).natTrans.naturality φ

/--
@isnad1 id=eq.1h9v.s9.4f69f5fe9e32 from=translated src=- shape=20cb0607 vocab=9e9fb003
-/
theorem baseChangeHom_counit (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullback π').map (baseChangeHom h F) ≫
        (pullbackPushforwardAdjunction π').counit.app ((pullback g').obj F) =
      (pullbackTwoSquare h).natTrans.app ((pushforward π).obj F) ≫
        (pullback g').map ((pullbackPushforwardAdjunction π).counit.app F) :=
  mateEquiv_counit (pullbackPushforwardAdjunction π) (pullbackPushforwardAdjunction π') (pullbackTwoSquare h) F

/--
@isnad1 id=eq.1h9v.s9.ce9d09be6383 from=translated src=- shape=bbd7dccb vocab=e32a8342
-/
theorem unit_baseChangeHom (h : g' ≫ π = π' ≫ ψ) (M : T.Modules) :
    (pullback ψ).map ((pullbackPushforwardAdjunction π).unit.app M) ≫ baseChangeHom h ((pullback π).obj M) =
      (pullbackPushforwardAdjunction π').unit.app ((pullback ψ).obj M) ≫
        (pushforward π').map ((pullbackTwoSquare h).natTrans.app M) :=
  unit_mateEquiv (pullbackPushforwardAdjunction π) (pullbackPushforwardAdjunction π') (pullbackTwoSquare h) M

section adjoint

variable (π ψ π' g')

/--
@isnad1 id=eq.1h4v.s9.3b91cf4bd1a9 from=translated src=- shape=6461db90 vocab=904adefc
-/
theorem conjugateEquiv_pullbackCongr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (e : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f) (pullbackCongr e).hom =
      (pushforwardCongr e).inv := by
  subst e
  have h1 : (pullbackCongr (rfl : f = f)).hom = 𝟙 _ := by simp [pullbackCongr]
  rw [h1, conjugateEquiv_id]
  ext M U : 3
  simp [pushforwardCongr_inv_app_app]

/--
@isnad1 id=eq.1h4v.s7.31c36036df1c from=translated src=- shape=febe99c3 vocab=5fb2e754
-/
theorem pushforwardCongr_symm_inv {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (e : f = g) :
    (pushforwardCongr e.symm).inv = (pushforwardCongr e).hom := by
  ext M U : 3
  simp [pushforwardCongr_inv_app_app, pushforwardCongr_hom_app_app]

/--
@isnad1 id=eq.0h5v.s10.7672f331c156 from=translated src=- shape=4859c43f vocab=95d66427
-/
theorem conjugateEquiv_pullbackComp_hom {W Y Z : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
        ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)) (pullbackComp f g).hom =
      (pushforwardComp f g).inv := by
  rw [← Iso.hom_comp_eq_id]
  rw [← conjugateEquiv_pullbackComp_inv f g]
  exact conjugateEquiv_comm _ _ (pullbackComp f g).hom_inv_id

/--
@isnad1 id=eq.1h8v.s10.910ae3853aa2 from=translated src=- shape=0cf6e5cd vocab=1dcd3c77
-/
theorem conjugateEquiv_pullbackTwoSquare (h : g' ≫ π = π' ≫ ψ) :
    conjugateEquiv ((pullbackPushforwardAdjunction π).comp (pullbackPushforwardAdjunction g'))
        ((pullbackPushforwardAdjunction ψ).comp (pullbackPushforwardAdjunction π'))
        (pullbackTwoSquare h).natTrans =
      (pushforwardComp g' π).hom ≫ (pushforwardCongr h).hom ≫ (pushforwardComp π' ψ).inv := by
  change conjugateEquiv _ _ ((pullbackComp π' ψ).hom ≫ (pullbackCongr h.symm).hom ≫ (pullbackComp g' π).inv) = _
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (π' ≫ ψ)),
    ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (g' ≫ π)),
    conjugateEquiv_pullbackComp_inv, conjugateEquiv_pullbackCongr_hom, pushforwardCongr_symm_inv,
    conjugateEquiv_pullbackComp_hom, Category.assoc]

/--
@isnad1 id=eq.1h9v.s10.b412c688ab64 from=translated src=- shape=d1173227 vocab=fea2340e
-/
theorem pullbackPushforwardAdjunction_homEquiv_baseChangeHom (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullbackPushforwardAdjunction ψ).homEquiv _ _ (baseChangeHom h F) =
      (pushforward π).map ((pullbackPushforwardAdjunction g').unit.app F) ≫
        (pushforwardComp g' π).hom.app _ ≫ (pushforwardCongr h).hom.app _ ≫ (pushforwardComp π' ψ).inv.app _ := by
  have key := unit_mateEquiv (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction ψ)
    (baseChangeNatTrans h) F
  have it := iterated_mateEquiv_conjugateEquiv (pullbackPushforwardAdjunction π)
    (pullbackPushforwardAdjunction π') (pullbackPushforwardAdjunction ψ) (pullbackPushforwardAdjunction g')
    (pullbackTwoSquare h)
  rw [conjugateEquiv_pullbackTwoSquare] at it
  have it' := NatTrans.congr_app it ((pullback g').obj F)
  simp only [NatTrans.comp_app] at it'
  rw [Adjunction.homEquiv_unit]
  have key' : (pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F) ≫
      (pushforward ψ).map ((baseChangeNatTrans h).natTrans.app F) =
      (pushforward π).map ((pullbackPushforwardAdjunction g').unit.app F) ≫
        (mateEquiv (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction ψ)
          (baseChangeNatTrans h)).app ((pullback g').obj F) := key.symm
  change (pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F) ≫
      (pushforward ψ).map ((baseChangeNatTrans h).natTrans.app F) = _
  rw [key']
  exact congrArg (fun t => (pushforward π).map ((pullbackPushforwardAdjunction g').unit.app F) ≫ t) it'

/--
@isnad1 id=eq.1h10v.s12.3f7c9eea9a1c from=translated src=- shape=71b44617 vocab=39f522bf
-/
theorem unit_app_app_comp_baseChangeHom_app (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) (U : T.Opens) :
    ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
        (baseChangeHom h F).app (ψ ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫
        ((pullback g').obj F).presheaf.map
          (eqToHom (show (π' ≫ ψ) ⁻¹ᵁ U = (g' ≫ π) ⁻¹ᵁ U by rw [h])).op := by
  have e := congrArg (fun t => Scheme.Modules.Hom.app t U) (pullbackPushforwardAdjunction_homEquiv_baseChangeHom π ψ π' g' h F)
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app] at e

  exact e

end adjoint

end AlgebraicGeometry.Scheme.Modules

end
