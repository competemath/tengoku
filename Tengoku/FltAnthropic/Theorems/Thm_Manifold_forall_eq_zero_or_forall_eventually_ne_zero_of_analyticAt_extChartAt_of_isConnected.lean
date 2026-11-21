import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

/--
@isnad1 id=or.3h3v.s8.6ea4583e2ce4 from=translated src=- shape=fb3e8eda vocab=4ac0850a
-/
theorem Manifold.forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M] [T2Space M]
    {W : Set M} (hW : IsOpen W) (hWc : IsConnected W) (g : M → ℂ)
    (hg : ∀ x ∈ W, AnalyticAt ℂ (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x)) :
    (∀ x ∈ W, g x = 0) ∨ (∀ x ∈ W, ∀ᶠ y in 𝓝[≠] x, g y ≠ 0) := by exact @_root_.P2MW.S_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected.solution M _ _ _ _ W hW hWc g hg
