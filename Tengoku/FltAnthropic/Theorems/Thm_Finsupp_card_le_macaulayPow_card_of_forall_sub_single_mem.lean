import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow
import Tengoku.FltAnthropic.P2M.Sol.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem
    (n d : ℕ) (hd : 1 ≤ d) (B : Finset (Fin (n + 1) →₀ ℕ)) (hB : ∀ m ∈ B, m.degree = d)
    (C : Finset (Fin (n + 1) →₀ ℕ)) (hC : ∀ u ∈ C, u.degree = d + 1)
    (hCB : ∀ u ∈ C, ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B) :
    C.card ≤ Nat.macaulayPow d B.card := by exact @_root_.P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.solution n d hd B hB C hC hCB
