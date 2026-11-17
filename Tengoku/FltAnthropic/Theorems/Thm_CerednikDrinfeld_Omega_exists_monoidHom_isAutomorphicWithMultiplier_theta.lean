import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

/--
@isnad1 id=ex.6h7v.s10.28fea5b839b6 from=translated src=- shape=17da48c0 vocab=dc542551
-/
theorem CerednikDrinfeld.Omega.exists_monoidHom_isAutomorphicWithMultiplier_theta
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hΘ : ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ a b z₀ z) :
    ∃ c : G →* Kˣ, (∀ β : G, (c β : K) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) ∧
      IsAutomorphicWithMultiplier ρ (upperHalfPlane K₀ K) (theta ρ a b z₀) c := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta.solution K₀ _ K _ _ _ _ _ _ G _ ρ a b z₀ ha hb hz₀ hz₀a hz₀b hΘ
