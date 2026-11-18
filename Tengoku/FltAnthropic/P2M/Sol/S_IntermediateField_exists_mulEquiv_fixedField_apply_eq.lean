import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_exists_mulEquiv_fixedField_apply_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_exists_mulEquiv_fixedField_apply_eq

set_option autoImplicit false

/--
@isnad1 id=ex.0h3v.s12.d47d7747e00c from=translated src=- shape=fca5eab9 vocab=98ffc961
-/
theorem solution
    (E F : Type) [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F] (H : Subgroup (F ≃ₐ[E] F)) :
    ∃ Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F), ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y := by
  refine ⟨(MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)), fun s y => ?_⟩
  rfl
