import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups
open _root_.CerednikDrinfeld.Omega hiding theta_pmoebius_pmoebius

theorem CerednikDrinfeld.Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ z₁ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz₁ : z₁ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hz₁a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₁) (hz₁b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₁)
    (hΘ : ∀ w ∈ upperHalfPlane K₀ K, ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ a b w z) (β : G) :
    theta ρ a b z₁ (pmoebius K₀ (ρ β) z₁) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint.solution K₀ _ K _ _ _ _ _ _ G _ ρ a b z₀ z₁ ha hb hz₀ hz₁ hz₀a hz₀b hz₁a hz₁b hΘ β
