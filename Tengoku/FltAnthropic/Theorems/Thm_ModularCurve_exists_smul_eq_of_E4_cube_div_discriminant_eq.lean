import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-simp] PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.exists_smul_eq_of_E4_cube_div_discriminant_eq (τ τ' : ℍ)
    (h : (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ =
      (ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by exact @_root_.P2MW.S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.solution τ τ' h
