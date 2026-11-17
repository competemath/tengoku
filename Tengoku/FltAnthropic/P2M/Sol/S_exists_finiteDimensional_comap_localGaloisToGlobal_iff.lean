import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.Theorems.Thm_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image
import Tengoku.FltAnthropic.Theorems.Thm_localGaloisToGlobal_mem_fixingSubgroup_iff
import Tengoku.FltAnthropic.Theorems.Thm_IntermediateField_exists_le_adjoin_padicEmbedding_image

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_exists_finiteDimensional_comap_localGaloisToGlobal_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_exists_finiteDimensional_comap_localGaloisToGlobal_iff

set_option autoImplicit false
open scoped IntermediateField
open Polynomial
open scoped Pointwise

/--
@isnad1 id=iff.0h3v.s11.9e03394058d1 from=translated src=- shape=d34655d4 vocab=aee1b925
-/
theorem solution
    (q : ℕ) [Fact q.Prime]
    (P : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Prop)
    (hP : ∀ U V, V ≤ U → P U → P V) :
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        P (F.fixingSubgroup.comap (localGaloisToGlobal q))) ↔
      ∃ K : IntermediateField ℚ_[q] (PadicAlgCl q), FiniteDimensional ℚ_[q] K ∧
        P K.fixingSubgroup := by
  constructor
  · rintro ⟨F, hF, h⟩
    refine ⟨IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ))),
      IntermediateField.finiteDimensional_adjoin_padicEmbedding_image q F, hP _ _ ?_ h⟩
    intro s hs
    rw [Subgroup.mem_comap]
    exact (localGaloisToGlobal_mem_fixingSubgroup_iff q F s).mpr hs
  · rintro ⟨K, hK, h⟩
    obtain ⟨F, hF, hKF⟩ := IntermediateField.exists_le_adjoin_padicEmbedding_image q K
    refine ⟨F, hF, hP _ _ ?_ h⟩
    intro s hs
    exact IntermediateField.fixingSubgroup_antitone hKF
      ((localGaloisToGlobal_mem_fixingSubgroup_iff q F s).mp hs)
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
