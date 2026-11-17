import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_RightConvolution
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField

theorem AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f (g * t) = rightConv K φ (fun y => f (t⁻¹ * y)) g := by exact @_root_.P2MW.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply.solution K _ _ φ f g t
