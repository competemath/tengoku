import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModPForms_one_mem_modPMod_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModPForms_one_mem_modPMod_zero

set_option autoImplicit false

open UpperHalfPlane

theorem solution (N : ℕ) (F : Type) [Field F] :
    (1 : PowerSeries F) ∈ ModPForms.modPMod N 0 F := by
  unfold ModPForms.modPMod
  refine Submodule.subset_span ⟨(1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0),
    fun n => if n = 0 then 1 else 0, fun n => ?_, ?_⟩
  · unfold ModularFormClass.qCoeff
    rw [ModularForm.qExpansion_one, PowerSeries.coeff_one]
    by_cases hn : n = 0 <;> simp [hn]
  · ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hn : n = 0 <;> simp [hn]
