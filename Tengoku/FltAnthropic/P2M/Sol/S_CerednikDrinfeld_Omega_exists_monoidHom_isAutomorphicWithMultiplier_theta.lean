import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import Tengoku.FltAnthropic.Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_eq_mul
import Tengoku.FltAnthropic.Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_pmoebius
import Tengoku.FltAnthropic.Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_mul_basePoint
import Tengoku.FltAnthropic.Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_mul_inv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace Law2Helpers

/--
@isnad1 id=iff.4h9v.s9.a887906ae936 from=translated src=- shape=d2d293b9 vocab=dd34496f
-/
theorem thetaMultipliable_pmoebius_pmoebius_iff
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b w z : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hw : w ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) (β : G) :
    ThetaMultipliable ρ a b (pmoebius K₀ (ρ β) w) (pmoebius K₀ (ρ β) z) ↔ ThetaMultipliable ρ a b w z := by
  rw [ThetaMultipliable, ThetaMultipliable, ← (Equiv.mulLeft β).multipliable_iff]
  refine multipliable_congr fun γ => ?_
  rw [Function.comp_apply, Equiv.coe_mulLeft, thetaFactor, thetaFactor, map_mul, pmoebius_mul K₀ ha,
    pmoebius_mul K₀ hb]
  exact CerednikDrinfeld.Omega.crossRatio_pmoebius (ρ β) hz hw (pmoebius_mem_upperHalfPlane K₀ ha _)
    (pmoebius_mem_upperHalfPlane K₀ hb _)

end Law2Helpers

/--
@isnad1 id=ex.6h7v.s10.28fea5b839b6 from=translated src=- shape=17da48c0 vocab=dc542551
-/
theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hΘ : ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ a b z₀ z) :
    ∃ c : G →* Kˣ, (∀ β : G, (c β : K) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) ∧
      IsAutomorphicWithMultiplier ρ (upperHalfPlane K₀ K) (theta ρ a b z₀) c := by
  have hm : ∀ β : G, ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β) z₀) := fun β =>
    hΘ _ (pmoebius_mem_upperHalfPlane K₀ hz₀ _)
  let u : G → Kˣ := fun β => Units.mkOfMulEqOne _ _
    (CerednikDrinfeld.Omega.theta_pmoebius_basePoint_mul_inv ρ ha hb hz₀ hz₀a hz₀b β (hm β) (hm β⁻¹))
  have hu : ∀ β, (u β : K) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) := fun β => rfl
  refine ⟨MonoidHom.mk' u fun β₁ β₂ => Units.ext ?_, fun β => rfl, fun β z hz => ?_⟩
  · rw [Units.val_mul, hu, hu, hu]
    exact CerednikDrinfeld.Omega.theta_pmoebius_mul_basePoint ρ ha hb hz₀ hz₀a hz₀b β₁ β₂ (hm β₁) (hm β₂)
  · rw [MonoidHom.mk'_apply, hu]
    have hinv : pmoebius K₀ (ρ β⁻¹) z₀ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hz₀ _
    have hB := CerednikDrinfeld.Omega.theta_pmoebius_pmoebius ρ ha hb hinv hz₀ β
    have hBiff := Law2Helpers.thetaMultipliable_pmoebius_pmoebius_iff ρ ha hb hinv hz₀ β
    rw [← pmoebius_mul K₀ hz₀, ← map_mul, mul_inv_cancel, map_one, pmoebius_one] at hB hBiff
    rw [CerednikDrinfeld.Omega.theta_pmoebius_eq_mul ρ ha hb hz₀ hz hz₀a hz₀b β (hΘ z hz) (hBiff.mp (hm β)), ← hB]
