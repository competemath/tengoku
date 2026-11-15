import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d)
    (y₀ : HH δ) (hy₀ : IsUnit ((∑ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (Pi.single y₀ 1)) y₀)) :
    (∀ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) =
        ∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) ∧
      Function.Bijective fun c : HH δ → B =>
        ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) (∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) := by exact @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply.solution g δ _ d _ hδd B _ hd ζ ω hζ hζu hω n e γ hγ y₀ hy₀
