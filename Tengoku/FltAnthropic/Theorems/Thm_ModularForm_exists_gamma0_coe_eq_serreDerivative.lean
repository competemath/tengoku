import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms
import Tengoku.Seed.NumberTheory.ModularForms.Derivative
import Tengoku.FltAnthropic.P2M.Sol.S_ModularForm_exists_gamma0_coe_eq_serreDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularForm_exists_gamma0_coe_eq_serreDerivative.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false

/--
@isnad1 id=ex.0h3v.s10.2829bf52f640 from=translated src=- shape=2f105c72 vocab=c357a9fb
-/
theorem ModularForm.exists_gamma0_coe_eq_serreDerivative (N' : ℕ) [NeZero N'] (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N') (k + 2),
      ⇑g = Derivative.serreDerivative (k : ℂ) ⇑f := by exact @_root_.P2MW.S_ModularForm_exists_gamma0_coe_eq_serreDerivative.solution N' _ k f
