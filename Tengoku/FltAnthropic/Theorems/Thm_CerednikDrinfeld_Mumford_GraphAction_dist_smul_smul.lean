import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Tengoku.Seed.Combinatorics.SimpleGraph.Metric
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem CerednikDrinfeld.Mumford.GraphAction.dist_smul_smul
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W)
    [CerednikDrinfeld.Mumford.GraphAction G 𝒯] (g : G) (x y : W) :
    𝒯.dist (g • x) (g • y) = 𝒯.dist x y := by exact @_root_.P2MW.S_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul.solution G _ W _ 𝒯 _ g x y
