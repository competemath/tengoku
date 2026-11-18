import Tengoku.Seed.NumberTheory.ModularForms.Basic
import Tengoku.Seed.Analysis.Meromorphic.Order
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

/--
@isnad1 id=ex.2h3v.s13.e68beb86628c from=translated src=- shape=44e54541 vocab=51ef07ce
-/
theorem ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (τ₀ σ₀ : ℍ) :
    ∃ U : Set ℍ, IsOpen U ∧ σ₀ ∈ U ∧ ∃ A ϑ : ℝ, 0 ≤ A ∧ 0 ≤ ϑ ∧ ϑ < 1 ∧
      ∀ (n : ℕ) (k : ℤ), 4 ≤ k →
        ∃ P : ModularForm Γ k,
          (∀ τ : ℍ, P τ = ∑' γ : ↥Γ,
            (((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
              ((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k)) ∧
          (∀ σ : ℍ, σ ∈ U →
            ‖P σ - ∑' γ : ↥Γ, Set.indicator {γ : ↥Γ | (γ : GL (Fin 2) ℝ) • σ₀ = τ₀} (fun γ : ↥Γ =>
              (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
              ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k)) γ‖
              ≤ A * ϑ ^ k * (2 * Real.sqrt (σ.im * τ₀.im)) ^ (-k)) := by exact @_root_.P2MW.S_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology.solution Γ hdet hdisc hcusp τ₀ σ₀
