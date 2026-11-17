import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_localGaloisToGlobal_mem_fixingSubgroup_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_localGaloisToGlobal_mem_fixingSubgroup_iff

set_option autoImplicit false
open scoped IntermediateField
open Polynomial
open scoped Pointwise

theorem solution
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (s : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) :
    localGaloisToGlobal q s ∈ F.fixingSubgroup ↔
      s ∈ (IntermediateField.adjoin ℚ_[q]
        (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      rw [← padicEmbedding_localGaloisToGlobal, h z hz]
    | algebraMap c => exact s.commutes c
    | add y z _ _ hy hz => rw [map_add, hy, hz]
    | mul y z _ _ hy hz => rw [map_mul, hy, hz]
    | inv y _ hy => rw [map_inv₀, hy]
  · intro h x hx
    have hfix := h (padicEmbedding q x) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    rw [← padicEmbedding_localGaloisToGlobal] at hfix
    exact (padicEmbedding q : AlgebraicClosure ℚ →+* PadicAlgCl q).injective hfix
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
