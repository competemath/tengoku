import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_theta_self_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_theta_self_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_self_eq_one
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    theta ρ a b z₀ z₀ = 1 := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_self_eq_one.solution K₀ _ K _ _ _ _ G _ ρ a b z₀ hz₀a hz₀b
