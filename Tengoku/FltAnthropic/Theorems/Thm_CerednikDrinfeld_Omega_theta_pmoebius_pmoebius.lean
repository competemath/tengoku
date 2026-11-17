import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_theta_pmoebius_pmoebius

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_theta_pmoebius_pmoebius.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

/--
@isnad1 id=eq.4h9v.s9.c7e773085f96 from=translated src=- shape=d57216f8 vocab=0b44b36a
-/
theorem CerednikDrinfeld.Omega.theta_pmoebius_pmoebius
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b w z : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hw : w ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) (β : G) :
    theta ρ a b (pmoebius K₀ (ρ β) w) (pmoebius K₀ (ρ β) z) = theta ρ a b w z := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_pmoebius.solution K₀ _ K _ _ _ _ G _ ρ a b w z ha hb hw hz β
