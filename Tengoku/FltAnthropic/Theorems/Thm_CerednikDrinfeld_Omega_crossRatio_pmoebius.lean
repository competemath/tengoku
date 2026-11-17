import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_crossRatio_pmoebius

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_pmoebius
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g : PGL(2, K₀)) {z z₀ x y : K}
    (hz : z ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hx : x ∈ upperHalfPlane K₀ K) (hy : y ∈ upperHalfPlane K₀ K) :
    crossRatio (pmoebius K₀ g z) (pmoebius K₀ g z₀) (pmoebius K₀ g x) (pmoebius K₀ g y) = crossRatio z z₀ x y := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius.solution K₀ _ K _ _ _ g z z₀ x y hz hz₀ hx hy
