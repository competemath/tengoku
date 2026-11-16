import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open _root_.CategoryTheory open _root_.AlgebraicGeometry open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.pullbackLocalSection)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app Hom.comp_app Modules Opens Modules.pullbackComp Modules.pullbackLocalSection)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (pullback Hom.comp_app pushforwardComp_hom_app_app Hom pushforward_map_app Hom.id_app Hom.app pullbackPushforwardAdjunction conjugateEquiv_pullbackComp_inv pullbackComp pullbackLocalSection pullbackLocalSection_def)
open _root_.AlgebraicGeometry.Scheme.Modules open _root_.AlgebraicGeometry.Scheme open _root_.AlgebraicGeometry

namespace PullbackCompSection

variable {Y : Scheme.{u}}

theorem pullbackComp_hom_app_pullbackLocalSection {X Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app ((pullbackComp f g).hom.app M) (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        (pullbackLocalSection f (pullbackLocalSection g s)) =
      (pullbackLocalSection (f ≫ g) s : Γ((Modules.pullback (f ≫ g)).obj M, f ⁻¹ᵁ (g ⁻¹ᵁ U))) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have h' := congr(Scheme.Modules.Hom.app $(h) U s)
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app] at h'

  rw [pullbackLocalSection_def f, pullbackLocalSection_def g, pullbackLocalSection_def (f ≫ g)]
  erw [h']
  have hid := congr(Scheme.Modules.Hom.app $((pullbackComp f g).inv_hom_id_app M) ((f ≫ g) ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U s))
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, Scheme.Modules.Hom.id_app,
    CategoryTheory.id_apply] at hid
  exact hid

end PullbackCompSection

end AlgebraicGeometry.Scheme.Modules

end

theorem solution
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection f
          (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection g s)) =
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection (f ≫ g) s :
        Γ((AlgebraicGeometry.Scheme.Modules.pullback (f ≫ g)).obj M, f ⁻¹ᵁ (g ⁻¹ᵁ U))) := by
  exact AlgebraicGeometry.Scheme.Modules.PullbackCompSection.pullbackComp_hom_app_pullbackLocalSection f g M U s
