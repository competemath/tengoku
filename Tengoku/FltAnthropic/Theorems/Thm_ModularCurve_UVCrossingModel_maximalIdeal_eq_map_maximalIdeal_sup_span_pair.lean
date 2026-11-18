import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

/--
@isnad1 id=eq.1h2v.s8.96f36e5e87ac from=translated src=- shape=738d0110 vocab=a68d2d5e
-/
theorem ModularCurve.UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair
    {W : Type*} [CommRing W] [IsLocalRing W] {π : W} (hπu : ¬IsUnit π) [IsLocalRing (UVCrossingModel W π)] :
    IsLocalRing.maximalIdeal (UVCrossingModel W π) =
      (IsLocalRing.maximalIdeal W).map (UVCrossingModel.constHom π) ⊔ Ideal.span {U π, V π} := by exact @_root_.P2MW.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair.solution W _ _ π hπu _
