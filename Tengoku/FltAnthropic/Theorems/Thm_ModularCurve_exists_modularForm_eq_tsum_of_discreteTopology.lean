import Tengoku.Seed.NumberTheory.ModularForms.Basic
import Tengoku.Seed.Analysis.Meromorphic.Order
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_exists_modularForm_eq_tsum_of_discreteTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_exists_modularForm_eq_tsum_of_discreteTopology.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_modularForm_eq_tsum_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (k : ℤ) (hk : 4 ≤ k)
    (φ : ℍ → ℂ) (hφ : MDiff φ)
    (hdecay : ∃ M : ℝ, ∀ w : ℍ, ‖φ w‖ * ‖(w : ℂ) + Complex.I‖ ^ k ≤ M) :

    (∀ τ₀ : ℍ, ∃ U : Set ℍ, IsOpen U ∧ τ₀ ∈ U ∧ ∃ u : ↥Γ → ℝ, Summable u ∧
        ∀ (γ : ↥Γ) (τ : ℍ), τ ∈ U → ‖φ ((γ : GL (Fin 2) ℝ) • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k)‖ ≤ u γ) ∧

    ∃ P : ModularForm Γ k, ∀ τ : ℍ, P τ = ∑' γ : ↥Γ, φ ((γ : GL (Fin 2) ℝ) • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k) := by exact @_root_.P2MW.S_ModularCurve_exists_modularForm_eq_tsum_of_discreteTopology.solution Γ hdet hdisc hcusp k hk φ hφ hdecay
