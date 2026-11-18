import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_laurentBaseChange_adjoin.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_laurentBaseChange_adjoin

open ModularCurve IntermediateField Polynomial

/--
@isnad1 id=eq.0h2v.s8.fb7c04aa20c3 from=translated src=- shape=475f1a40 vocab=22f6ccf6
-/
theorem solution (L : Type*) [Field L] [Algebra ℚ L] (S : Set (LaurentSeries ℚ)) : ModularCurve.laurentBaseChange L (IntermediateField.adjoin ℚ S) = IntermediateField.adjoin L (ModularCurve.coeffEmb L '' S) := by
  apply le_antisymm
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hle : (IntermediateField.adjoin ℚ S).toSubfield ≤
        (IntermediateField.adjoin L (coeffEmb L '' S)).toSubfield.comap (coeffEmb L) := by
      rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.mpr ?_
      rintro x (⟨c, rfl⟩ | hx)
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        have : coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c)
            = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
          rw [algebraMap_apply_eq_single, coeffEmb, coeffMap_single,
            ← algebraMap_laurentSeries_eq_single]
        rw [this]
        exact (IntermediateField.adjoin L (coeffEmb L '' S)).algebraMap_mem _
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        exact IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩
    exact hle hy
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L (IntermediateField.subset_adjoin ℚ S hy)
