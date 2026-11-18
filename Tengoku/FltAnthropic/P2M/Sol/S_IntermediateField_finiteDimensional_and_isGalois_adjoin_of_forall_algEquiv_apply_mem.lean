import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem

set_option autoImplicit false

universe u v

theorem solution
    (K : Type u) [Field K] (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (S : Set Ω) (hS : S.Finite) (hsep : ∀ x ∈ S, IsSeparable K x)
    (hstab : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ S, σ x ∈ S) :
    FiniteDimensional K ↥(IntermediateField.adjoin K S) ∧ IsGalois K ↥(IntermediateField.adjoin K S) := by
  haveI : Finite ↑S := hS.to_subtype
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hfd : FiniteDimensional K ↥(IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (hsep x hx).isIntegral
  haveI : Algebra.IsSeparable K ↥(IntermediateField.adjoin K S) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K Ω).mpr hsep
  haveI : Normal K ↥(IntermediateField.adjoin K S) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    intro σ
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, hx, rfl⟩
    exact hstab σ x hx
  exact ⟨hfd, IsGalois.mk⟩
