import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_mem_gam.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_mem_gam

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d) :
    ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U := by
  obtain ⟨y₀, hy₀⟩ := AlgebraicGeometry.ThetaLevel.exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam δ d hδd B hd ζ ω hζ hζu hω e γ hγ
  obtain ⟨hv, hbij⟩ := AlgebraicGeometry.ThetaLevel.forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply
    δ d hδd B hd ζ ω hζ hζu hω e γ hγ y₀ hy₀
  exact AlgebraicGeometry.ThetaLevel.exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective δ d hδd B hd ζ ω hζ hζu hω e γ hγ _ hv hbij
