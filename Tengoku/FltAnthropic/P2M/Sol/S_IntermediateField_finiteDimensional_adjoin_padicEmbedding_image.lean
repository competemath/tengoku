import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image

set_option autoImplicit false
open scoped IntermediateField
open Polynomial
open scoped Pointwise

/--
@isnad1 id=finitedi.0h2v.s11.b6140a9a4402 from=translated src=- shape=0f4379ab vocab=d1e7ac10
-/
theorem solution
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    FiniteDimensional ℚ_[q]
      (IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))) := by
  classical
  let bF := Module.finBasis ℚ F
  let T : Set (PadicAlgCl q) := Set.range fun i => padicEmbedding q (bF i)
  haveI : FiniteDimensional ℚ_[q] (IntermediateField.adjoin ℚ_[q] T) :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[q]) x).isIntegral)
  have hle : IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ))) ≤
      IntermediateField.adjoin ℚ_[q] T := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : AlgebraicClosure ℚ) = F.val.toLinearMap (⟨x, hx⟩ : F) := rfl
    rw [hx', ← bF.sum_repr (⟨x, hx⟩ : F), map_sum]
    change (padicEmbedding q).toLinearMap _ ∈ _
    rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ ℚ_[q] (PadicAlgCl q)]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
