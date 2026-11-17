import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_mul_basePoint
import Tengoku.FltAnthropic.Theorems.Thm_CerednikDrinfeld_Omega_theta_self_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_mul_inv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_mul_inv

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

/--
@isnad1 id=eq.7h8v.s11.3ec1586c7538 from=translated src=- shape=410deec6 vocab=fcfd235f
-/
theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (β : G)
    (h : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β) z₀))
    (h' : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β⁻¹) z₀)) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) * theta ρ a b z₀ (pmoebius K₀ (ρ β⁻¹) z₀) = 1 := by
  rw [← CerednikDrinfeld.Omega.theta_pmoebius_mul_basePoint ρ ha hb hz₀ hz₀a hz₀b β β⁻¹ h h', mul_inv_cancel,
    map_one, pmoebius_one, CerednikDrinfeld.Omega.theta_self_eq_one ρ hz₀a hz₀b]
