import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_theta_mul_theta_basePoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_theta_mul_theta_basePoint.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups
open _root_.CerednikDrinfeld.Omega hiding crossRatio_mul_crossRatio

/--
@isnad1 id=eq.4h9v.s9.9299e5432d1f from=translated src=- shape=64ce00b4 vocab=b4991957
-/
theorem CerednikDrinfeld.Omega.theta_mul_theta_basePoint
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ z w : K}
    (hza : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z) (hzb : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z)
    (h₀ : ThetaMultipliable ρ a b z₀ z) (h₁ : ThetaMultipliable ρ a b z w) :
    theta ρ a b z₀ z * theta ρ a b z w = theta ρ a b z₀ w := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_mul_theta_basePoint.solution K₀ _ K _ _ _ _ _ _ G _ ρ a b z₀ z w hza hzb h₀ h₁
