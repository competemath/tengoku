import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=isnoethe.0h2v.s4.2581ed7f22fa from=translated src=- shape=65f277ad vocab=897e9348
-/
theorem MvPowerSeries.isNoetherianRing_fin_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by exact @_root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing.solution R _ _ n
