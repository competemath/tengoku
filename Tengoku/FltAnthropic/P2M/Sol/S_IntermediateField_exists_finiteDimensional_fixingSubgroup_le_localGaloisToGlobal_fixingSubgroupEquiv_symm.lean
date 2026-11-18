import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.Theorems.Thm_localGaloisToGlobal_mem_fixingSubgroup_iff
import Tengoku.FltAnthropic.Theorems.Thm_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory

open IntermediateField in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
      ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup →
        ((localGaloisToGlobal q).comp
        (K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)) σ ∈ F.fixingSubgroup := by
  classical
  let Ω := PadicAlgCl q
  let ι : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[ℚ_[q]] Ω) :=
    K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom
  have hι : ∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), ι σ x = σ x := fun _ _ => rfl
  let KF : IntermediateField ℚ_[q] Ω := IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))
  haveI : FiniteDimensional ℚ_[q] KF := IntermediateField.finiteDimensional_adjoin_padicEmbedding_image q F
  haveI : FiniteDimensional ℚ_[q] (K ⊔ KF : IntermediateField ℚ_[q] Ω) := IntermediateField.finiteDimensional_sup K KF
  let E : IntermediateField K Ω := IntermediateField.extendScalars (le_sup_left : K ≤ K ⊔ KF)
  haveI : FiniteDimensional K E := by
    haveI : FiniteDimensional ℚ_[q] E := ‹FiniteDimensional ℚ_[q] (K ⊔ KF : IntermediateField ℚ_[q] Ω)›
    exact Module.Finite.of_restrictScalars_finite ℚ_[q] K E
  refine ⟨E, inferInstance, fun σ hσ => ?_⟩
  show localGaloisToGlobal q (ι σ) ∈ F.fixingSubgroup
  rw [localGaloisToGlobal_mem_fixingSubgroup_iff]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  rw [hι]
  exact hσ x ((IntermediateField.mem_extendScalars (le_sup_left : K ≤ K ⊔ KF)).2 (le_sup_right (a := K) hx))
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
