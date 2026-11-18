import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModPForms_modPCusp_le_modPMod.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModPForms_modPCusp_le_modPMod
set_option autoImplicit false

open ModPForms

theorem solution (N' : ℕ) [NeZero N'] (k : ℤ) (F : Type) [Field F] :
    modPCusp N' k F ≤ modPMod N' k F := by
  refine Submodule.span_mono ?_
  rintro φ ⟨f, a, ha, hφ⟩
  exact ⟨(f : ModularForm (CongruenceSubgroup.Gamma0 N') k), a, ha, hφ⟩
