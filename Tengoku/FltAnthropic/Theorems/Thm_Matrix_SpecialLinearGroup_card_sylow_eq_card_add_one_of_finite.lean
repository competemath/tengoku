import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-simp] ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe

set_option autoImplicit false

open Matrix MatrixGroups

theorem Matrix.SpecialLinearGroup.card_sylow_eq_card_add_one_of_finite
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (G : Subgroup SL(2, K)) [Finite G] (P : Sylow p G)
    (hq : 3 < Nat.card P) (hP : Nat.card (Sylow p G) ≠ 1) :
    Nat.card (Sylow p G) = Nat.card P + 1 := by exact @_root_.P2MW.S_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite.solution K _ p _ _ hp2 G _ P hq hP
