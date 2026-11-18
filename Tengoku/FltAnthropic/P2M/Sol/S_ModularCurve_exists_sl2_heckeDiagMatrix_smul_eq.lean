import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_HeckeOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ModularCurve

namespace QexpN

open Matrix.SpecialLinearGroup ModularForm

private theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private def conjSL {p : ℕ} (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) : SL(2, ℤ) :=
  ⟨!![g 0 0, p * g 0 1; e, g 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination det_eq g + g 0 1 * he⟩

end QexpN

end ModularCurve

end
