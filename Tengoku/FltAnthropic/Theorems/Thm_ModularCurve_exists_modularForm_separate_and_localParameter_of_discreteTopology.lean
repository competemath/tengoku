import Tengoku.Seed.NumberTheory.ModularForms.Basic
import Tengoku.Seed.Analysis.Meromorphic.Order
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

/--
@isnad1 id=and.3h1v.s12.0873f329b29f from=translated src=- shape=124711b0 vocab=3ed7a1fc
-/
theorem ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ) :

    (∀ τ σ : ℍ, (∀ γ ∈ Γ, γ • τ ≠ σ) →
      ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, g τ * h σ ≠ g σ * h τ) ∧

    (∀ τ : ℍ, ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, h τ ≠ 0 ∧
      meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) =
        (((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) : WithTop ℤ)) := by exact @_root_.P2MW.S_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology.solution Γ hdet hneg hdisc hcusp
