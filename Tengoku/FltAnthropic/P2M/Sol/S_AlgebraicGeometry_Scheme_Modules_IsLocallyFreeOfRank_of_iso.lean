import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso

universe u
open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=islocall.1h5v.s4.7a14efcc206f from=translated src=- shape=8e01430a vocab=3c791026
-/
theorem solution {X : Scheme.{u}} {n : ℕ} {M N : X.Modules} (e : M ≅ N) (h : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsLocallyFreeOfRank n N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨i⟩⟩ := h.exists_trivialization x
  exact ⟨U, hx, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ i⟩⟩
