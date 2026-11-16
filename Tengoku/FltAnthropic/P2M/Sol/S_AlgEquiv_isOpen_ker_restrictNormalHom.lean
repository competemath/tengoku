import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgEquiv_isOpen_ker_restrictNormalHom.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgEquiv_isOpen_ker_restrictNormalHom

set_option autoImplicit false

theorem solution (K L : Type*) [Field K] [Field L] [Algebra K L]
    (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Normal K E]
    [FiniteDimensional K E] :
    IsOpen ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker : Set (L ≃ₐ[K] L)) := by
  let ι : E →ₐ[K] L := IsScalarTower.toAlgHom K E L
  let L' : IntermediateField K L := ι.fieldRange
  haveI : FiniteDimensional K L' := Module.Finite.equiv
    (((IntermediateField.topEquiv (F := K) (E := E)).symm.trans (IntermediateField.equivMap ⊤ ι)).trans
      (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map ι).symm)).toLinearEquiv
  apply Subgroup.isOpen_mono (H₁ := L'.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen L')
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  rw [MonoidHom.mem_ker]
  apply AlgEquiv.ext
  intro y
  apply (algebraMap E L).injective
  have hc := AlgEquiv.restrictNormal_commutes σ E y
  change algebraMap E L ((σ.restrictNormal E) y) = algebraMap E L ((1 : E ≃ₐ[K] E) y)
  rw [AlgEquiv.one_apply, hc]
  exact hσ _ (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)
