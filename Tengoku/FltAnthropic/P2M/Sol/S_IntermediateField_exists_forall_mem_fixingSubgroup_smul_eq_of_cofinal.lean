import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal

set_option autoImplicit false

universe u v

open IntermediateField

theorem solution
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hcof : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (x : Ωˣ) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ • x = x := by
  obtain ⟨E, hE, h⟩ := exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq (K := K) x
  obtain ⟨F, hF, hFE⟩ := hcof E hE
  exact ⟨F, hF, fun σ hσ => h σ (hFE σ hσ)⟩
