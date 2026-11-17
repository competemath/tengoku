import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_QCoeffLinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_qCoeffLinear_apply.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_qCoeffLinear_apply

/--
@isnad1 id=eq.0h4v.s10.c33927cec1d3 from=translated src=- shape=a50a7afa vocab=0da4d753
-/
theorem solution (M : ℕ) (k : ℤ) (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    CuspForm.qCoeffLinear M k n f = ModularFormClass.qCoeff (⇑f) n := rfl
