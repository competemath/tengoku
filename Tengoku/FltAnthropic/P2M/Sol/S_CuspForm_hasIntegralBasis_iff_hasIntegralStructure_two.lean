import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_IntegralLattice
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_IntegralStructure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two

theorem solution (N : ℕ) : CuspForm.HasIntegralBasis N ↔ CuspForm.HasIntegralStructure N 2 := by
  have hset : CuspForm.qIntegralSet N =
      {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2 | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)} := by
    ext f
    simp only [CuspForm.qIntegralSet, Set.mem_ofPred_eq]
    refine forall_congr' fun n => ?_
    rw [Subring.mem_bot]
    exact ⟨fun ⟨m, hm⟩ => ⟨m, hm.symm⟩, fun ⟨m, hm⟩ => ⟨m, hm.symm⟩⟩
  unfold CuspForm.HasIntegralBasis CuspForm.HasIntegralStructure CuspForm.intLattice
  rw [hset, Submodule.span_span_of_tower]
