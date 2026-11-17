import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups
open _root_.CerednikDrinfeld.Omega hiding theta_pmoebius_basePoint_mul_inv

/--
@isnad1 id=eq.6h9v.s10.3d43dbaefdc1 from=translated src=- shape=b496fe53 vocab=47a70192
-/
theorem CerednikDrinfeld.Omega.period_eq_period_of_mem_upperHalfPlane
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a a' z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (ha' : a' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀a' : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀)
    (hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ z ∈ upperHalfPlane K₀ K,
      ThetaMultipliable ρ x y z₀ z)
    (α β : G) :
    period ρ a z₀ α β = period ρ a' z₀ α β := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane.solution K₀ _ K _ _ _ _ _ _ G _ ρ a a' z₀ ha ha' hz₀ hz₀a hz₀a' hΘ α β
