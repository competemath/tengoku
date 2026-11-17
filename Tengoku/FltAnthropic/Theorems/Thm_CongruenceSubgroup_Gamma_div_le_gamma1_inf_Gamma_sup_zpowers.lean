import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CongruenceSubgroup.Gamma_div_le_gamma1_inf_Gamma_sup_zpowers
    (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N) :
    Gamma (N / p) ≤ (Gamma1 N ⊓ Gamma (N / p ^ N.factorization p)) ⊔
      Subgroup.zpowers (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) := by exact @_root_.P2MW.S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers.solution N p _ hp hpN
