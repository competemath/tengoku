import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.lean`: wrote out 9 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 2 `p2m_open`, 4 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.AlgebraicGeometry

open Opposite TopologicalSpace

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules.hom_ext Modules.Hom.app_smul ringCatSheaf Modules.pushforward Modules.pullback Hom Γ Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor Modules.restrictFunctorIsoPullback restrictFunctor Modules.pullbackCongr Modules.Hom.isIso_iff_isIso_app Modules.pullbackPushforwardAdjunction Modules Opens Modules.map_smul Opens.opensRange_ι PresheafOfModules Modules.pullbackComp)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (hom_ext Hom.app_smul pushforward pullback presheaf Hom mapPresheaf_app restrictFunctor restrictFunctorIsoPullback pullbackCongr Hom.isIso_iff_isIso_app pullbackPushforwardAdjunction map_smul pullbackComp)
open _root_.AlgebraicGeometry.Scheme.Modules open _root_.AlgebraicGeometry.Scheme open _root_.AlgebraicGeometry

namespace FramePullback

scoped instance opensMap_final' {X Y : Scheme.{u}} (f : X ⟶ Y) : (Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

variable {Z : Scheme.{u}}

section pullback

variable {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules)

omit M in
lemma image_preimage_eq {W V : X'.Opens} (hW : W ≤ V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W :=
  (Scheme.Hom.image_preimage_eq_opensRange_inf V.ι W).trans
    (by rw [Scheme.Opens.opensRange_ι]; exact inf_eq_right.mpr hW)

end pullback

end FramePullback
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules.FramePullback

end AlgebraicGeometry.Scheme.Modules
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules.FramePullback _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules.FramePullback _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules.FramePullback _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry
