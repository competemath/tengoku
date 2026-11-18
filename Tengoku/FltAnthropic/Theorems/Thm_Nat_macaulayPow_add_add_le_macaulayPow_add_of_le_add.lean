import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow
import Tengoku.FltAnthropic.P2M.Sol.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Nat.macaulayPow_add_add_le_macaulayPow_add_of_le_add
    (d x y u v : ℕ) (hd : 1 ≤ d) (hx : x ≤ u + v)
    (hu : Nat.macaulayPow d u + y ≤ Nat.macaulayPow d y)
    (hv : Nat.macaulayPow (d + 1) v + x ≤ Nat.macaulayPow (d + 1) x) :
    Nat.macaulayPow (d + 1) x + (x + y) ≤ Nat.macaulayPow (d + 1) (x + y) := by exact @_root_.P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.solution d x y u v hd hx hu hv
