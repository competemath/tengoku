import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IntermediateField
/--
@isnad1 id=ex.0h3v.s9.909e022d7362 from=translated src=- shape=26b99f78 vocab=f93eef47
-/
theorem IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ωˣ) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ • x = x := by exact @_root_.P2MW.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq.solution K Ω _ _ _ _ x
