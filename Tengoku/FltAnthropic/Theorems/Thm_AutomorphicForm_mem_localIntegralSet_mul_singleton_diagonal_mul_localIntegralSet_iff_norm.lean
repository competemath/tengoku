import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletion K) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ ≤ 1) (m₁ m₂ : ℤ) (hm : m₂ ≤ m₁)
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![π ^ m₁, π ^ m₂])
    (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
        AutomorphicForm.localIntegralSet K v ↔
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = ‖π‖ ^ (m₁ + m₂) ∧
      (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ ‖π‖ ^ m₂) ∧
      ∃ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ = ‖π‖ ^ m₂ := by exact @_root_.P2MW.S_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm.solution K _ _ v π hπ0 hπ1 m₁ m₂ hm dl hdl g
