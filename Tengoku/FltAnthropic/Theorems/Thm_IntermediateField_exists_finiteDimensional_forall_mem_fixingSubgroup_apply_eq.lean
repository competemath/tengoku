import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IntermediateField
/--
@isnad1 id=ex.0h3v.s8.8a19562f699e from=translated src=- shape=f417e289 vocab=f8d3a08f
-/
theorem IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ω) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ x = x := by exact @_root_.P2MW.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq.solution K Ω _ _ _ _ x
