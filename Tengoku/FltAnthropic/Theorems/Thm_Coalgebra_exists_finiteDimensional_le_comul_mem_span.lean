import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Coalgebra_exists_finiteDimensional_le_comul_mem_span

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Coalgebra_exists_finiteDimensional_le_comul_mem_span.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Coalgebra.exists_finiteDimensional_le_comul_mem_span
    {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (K : Submodule k C)
    (hK : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (x : C) (hx : x ∈ K) :
    ∃ D : Submodule k C, D ≤ K ∧ FiniteDimensional k ↥D ∧ x ∈ D ∧
      ∀ y ∈ D, Coalgebra.comul (R := k) y ∈
        Submodule.span k {t : C ⊗[k] C | ∃ a ∈ D, ∃ b ∈ D, t = a ⊗ₜ[k] b} := by exact @_root_.P2MW.S_Coalgebra_exists_finiteDimensional_le_comul_mem_span.solution k _ C _ _ _ K hK x hx
