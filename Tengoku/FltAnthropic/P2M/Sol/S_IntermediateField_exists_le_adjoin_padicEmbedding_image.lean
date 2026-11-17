import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.Theorems.Thm_PadicAlgCl_exists_mem_adjoin_padicEmbedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_exists_le_adjoin_padicEmbedding_image.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_exists_le_adjoin_padicEmbedding_image

set_option autoImplicit false
open scoped IntermediateField
open Polynomial
open scoped Pointwise

/--
@isnad1 id=ex.0h2v.s10.f4bf1f85844b from=translated src=- shape=f6831683 vocab=e8b1ed21
-/
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      K ≤ IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ))) := by
  classical
  let bK := Module.finBasis ℚ_[q] K
  choose β hβ using fun i => PadicAlgCl.exists_mem_adjoin_padicEmbedding q ((bK i : K) : PadicAlgCl q)
  refine ⟨IntermediateField.adjoin ℚ (Set.range β),
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral), ?_⟩
  intro x hx
  have hx' : x = K.val.toLinearMap (⟨x, hx⟩ : K) := rfl
  rw [hx', ← bK.sum_repr (⟨x, hx⟩ : K), map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_smul]
  refine IntermediateField.smul_mem _ ?_
  have hle : ℚ_[q]⟮padicEmbedding q (β i)⟯ ≤
      IntermediateField.adjoin ℚ_[q] (padicEmbedding q ''
        (IntermediateField.adjoin ℚ (Set.range β) : Set (AlgebraicClosure ℚ))) :=
    IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.subset_adjoin _ _ ⟨β i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩, rfl⟩)
  exact hle (hβ i)
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
