import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.FltAnthropic.P2M.Sol.S_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false

/--
@isnad1 id=ex.2h2v.s9.0c78b5815ba6 from=translated src=- shape=e6177bfd vocab=289dea50
-/
theorem ModularForm.exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] :
    ∃ (A : ModularForm (CongruenceSubgroup.Gamma0 N') ((p : ℤ) - 1)) (b : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff A n = (b n : ℂ)) ∧ (p : ℤ) ∣ b 0 - 1 ∧ ∀ n, 0 < n → (p : ℤ) ∣ b n := by exact @_root_.P2MW.S_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le.solution p hp hp5 N' _
