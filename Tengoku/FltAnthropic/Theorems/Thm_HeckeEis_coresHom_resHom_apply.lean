import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_coresHom_resHom_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_coresHom_resHom_apply.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Subgroup
/--
@isnad1 id=eq.0h5v.s12.73700adb306b from=translated src=- shape=238fc22e vocab=93837408
-/
theorem HeckeEis.coresHom_resHom_apply {G : Type*} [Group G] (H : Subgroup G) {A : Type*}
    [AddCommGroup A] [H.FiniteIndex] (φ : Additive G →+ A) (g : G) :
    HeckeEis.coresHom H (HeckeEis.resHom H φ) (Additive.ofMul g) =
      H.index • φ (Additive.ofMul g) := by exact @_root_.P2MW.S_HeckeEis_coresHom_resHom_apply.solution G _ H A _ _ φ g
