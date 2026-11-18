import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq

set_option autoImplicit false

universe u v

open IntermediateField

theorem solution
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ωˣ) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ • x = x := by
  obtain ⟨E, hE, h⟩ := exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq (K := K) (x : Ω)
  exact ⟨E, hE, fun σ hσ => Units.ext (h σ hσ)⟩
