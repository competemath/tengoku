import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv

universe u

open CategoryTheory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules

/--
@isnad1 id=eq.0h7v.s11.4dc326cf3bab from=translated src=- shape=579fc4f0 vocab=3aabad1b
-/
theorem solution
    {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).unit.app M).app U ≫
        ((Scheme.Modules.pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback f).obj M)).app (f ⁻¹ᵁ U) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction g))
    (pullbackPushforwardAdjunction (g ≫ f)) (pullbackComp g f).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun t => Hom.app t U) h
  simp only [Hom.comp_app, Adjunction.comp_unit_app, pushforward_map_app, pushforwardComp_hom_app_app,
    Functor.comp_obj] at h'
  erw [Category.comp_id] at h'
  exact h'.symm
