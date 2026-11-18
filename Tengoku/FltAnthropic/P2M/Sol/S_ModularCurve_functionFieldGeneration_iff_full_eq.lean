import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_functionFieldGeneration_iff_full_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_functionFieldGeneration_iff_full_eq

open ModularCurve IntermediateField

noncomputable section

/--
@isnad1 id=iff.0h1v.s6.bb5eca17272c from=translated src=- shape=6aad3ccd vocab=596e0bf6
-/
theorem solution (N : ℕ) [NeZero N] : FunctionFieldGeneration N ↔ modularFunctionFieldFull N = modularFunctionField N :=by
  constructor
  · intro hgen
    refine le_antisymm ?_ (modularFunctionField_le_full N)
    rw [modularFunctionFieldFull, adjoin_le_iff]
    rintro x ⟨d, hne, hdvd, rfl⟩
    exact hgen d hdvd hne
  · intro heq d hdvd hne
    haveI := hne
    show qExpand ℚ d jq ∈ modularFunctionField N
    rw [← heq]
    exact jqd_mem_full N hdvd

end
