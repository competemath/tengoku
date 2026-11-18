import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EisensteinSeries_EisensteinG
import Tengoku.FltAnthropic.P2M.Sol.S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Matrix
open scoped MatrixGroups CongruenceSubgroup ModularForm

theorem EisensteinSeries.exists_modularForm_coe_eq_eisensteinG
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    (∃ F : ModularForm Γ(N) k, ⇑F = EisensteinSeries.eisensteinG N k a) ∧
      ∀ γ : SL(2, ℤ), EisensteinSeries.eisensteinG N k a ∣[k] γ =
        EisensteinSeries.eisensteinG N k (a ᵥ* γ) := by exact @_root_.P2MW.S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.solution N _ k hk a
