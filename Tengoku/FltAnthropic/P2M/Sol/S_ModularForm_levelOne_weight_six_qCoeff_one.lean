import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.Seed.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_levelOne_weight_six_qCoeff_one.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_levelOne_weight_six_qCoeff_one
open scoped MatrixGroups

namespace ModularForm export _root_.ModularForm (levelOne_weight_six_rank_one E₆ E₆_qExpansion_coeff_one) end ModularForm
open scoped _root_.ModularForm in
private theorem ModularForm.levelOne_weight_six_qCoeff_one (Y : ModularForm 𝒮ℒ 6) : ModularFormClass.qCoeff ⇑Y 1 = -504 * ModularFormClass.qCoeff ⇑Y 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₆ = Y :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₆ (EisensteinSeries.E_ne_zero _ ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_six_rank_one) Y
  have hq : UpperHalfPlane.qExpansion 1 ⇑Y = c • UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c ModularForm.E₆,
      show (c • ⇑ModularForm.E₆) = ⇑Y from congrArg DFunLike.coe hc]
  have h0 : (UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  show (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 1 = _ * (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 0
  rw [hq, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul, h0,
    ModularForm.E₆_qExpansion_coeff_one]
  ring

/--
@isnad1 id=eq.0h1v.s9.84d0d2a3c7a8 from=translated src=- shape=5aa86482 vocab=579687ce
-/
theorem solution (Y : ModularForm 𝒮ℒ 6) : ModularFormClass.qCoeff ⇑Y 1 = -504 * ModularFormClass.qCoeff ⇑Y 0 :=
  ModularForm.levelOne_weight_six_qCoeff_one Y
