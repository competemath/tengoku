import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens

universe u
open _root_.CategoryTheory open _root_.AlgebraicGeometry open _root_.Opposite open _root_.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules.pullback Modules Opens Modules.IsLocallyFreeOfRank)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (pullback pullbackCongr pullbackComp IsLocallyFreeOfRank)
open _root_.AlgebraicGeometry.Scheme.Modules open _root_.AlgebraicGeometry.Scheme open _root_.AlgebraicGeometry

/--
@isnad1 id=final.0h3v.s7.e0f065c98e32 from=translated src=- shape=5f26ffc8 vocab=6d7edeab
-/
theorem opensMap_final' {X Y : Scheme.{u}} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

end AlgebraicGeometry.Scheme.Modules
