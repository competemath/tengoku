import Tengoku.Seed.NumberTheory.ModularForms.Basic
import Tengoku.Seed.Analysis.Meromorphic.Order
import Tengoku.FltAnthropic.P2M.Sol.S_UpperHalfPlane_denom_eq_of_smul_eq_self

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_UpperHalfPlane_denom_eq_of_smul_eq_self.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

/--
@isnad1 id=and.2h2v.s11.0b36a3cbe04f from=translated src=- shape=25116786 vocab=26799296
-/
theorem UpperHalfPlane.denom_eq_of_smul_eq_self
    (g : GL (Fin 2) ℝ) (hg : Matrix.GeneralLinearGroup.det g = 1) (τ₀ : ℍ) (hfix : g • τ₀ = τ₀) :
    ‖denom g τ₀‖ = 1 ∧
    (∀ τ : ℍ, (((g • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) * denom g τ = ((τ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) * denom g τ₀) ∧
    (∀ τ : ℍ, (((g • τ : ℍ) : ℂ) - (τ₀ : ℂ)) * denom g τ * denom g τ₀ = (τ : ℂ) - (τ₀ : ℂ)) ∧
    (denom g τ₀ = 1 → g = 1) ∧
    (∀ h : GL (Fin 2) ℝ, Matrix.GeneralLinearGroup.det h = 1 → h • τ₀ = τ₀ → denom (g * h) τ₀ = denom g τ₀ * denom h τ₀) := by exact @_root_.P2MW.S_UpperHalfPlane_denom_eq_of_smul_eq_self.solution g hg τ₀ hfix
