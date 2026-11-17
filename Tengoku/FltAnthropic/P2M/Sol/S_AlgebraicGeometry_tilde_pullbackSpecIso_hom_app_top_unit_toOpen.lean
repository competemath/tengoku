import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ModulesTildePullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.AlgebraicGeometry open _root_.Opposite open _root_.TensorProduct

namespace AlgebraicGeometry export _root_.AlgebraicGeometry (Scheme.Modules.pushforward tilde.adjunction moduleSpecΓFunctor Spec Spec.map Scheme pullbackSpecIso Scheme.Modules.pullbackPushforwardAdjunction tilde.functor Scheme.Modules tilde tilde.toOpen Scheme.Modules.pushforwardSpecCompΓIso tilde.pullbackSpecIso) namespace tilde export _root_.AlgebraicGeometry.tilde (adjunction toOpen pullbackSpecIso) end AlgebraicGeometry.tilde
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.tilde in

theorem AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat.{u} R) :
    ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h : ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom =
      ((((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
        (Scheme.Modules.pushforwardSpecCompΓIso φ).symm).unit.app M) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom] at h
  rw [Adjunction.comp_unit_app (ModuleCat.extendRestrictScalarsAdj φ.hom)] at h
  have h2 := congrArg (· ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
    ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h2
  exact h2

theorem solution {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat.{u} R) (m : M) :
    ((tilde.pullbackSpecIso φ M).hom.app ⊤).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤).hom
        ((tilde.toOpen M ⊤).hom m)) =
    (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom ((1 : S) ⊗ₜ m) := by
  have h := congrArg (fun ψ => ψ.hom m) (AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux φ M)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Adjunction.comp_unit_app, Functor.comp_map] at h
  exact h

