import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq

set_option autoImplicit false

universe u v

open IntermediateField

/--
@isnad1 id=ex.0h3v.s8.8a19562f699e from=translated src=- shape=f417e289 vocab=f8d3a08f
-/
theorem solution
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ω) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ x = x := by
  exact
    ⟨IntermediateField.adjoin K {x},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x),
      fun σ hσ => (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ x
        (IntermediateField.subset_adjoin K _ (Set.mem_singleton x))⟩
