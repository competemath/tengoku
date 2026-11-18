import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow
import Tengoku.FltAnthropic.P2M.Sol.S_Nat_macaulayPow_lt_macaulayPow_of_lt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Nat_macaulayPow_lt_macaulayPow_of_lt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=lt.2h3v.s4.fd7c94b92438 from=translated src=- shape=aad03d02 vocab=958acc08
-/
theorem Nat.macaulayPow_lt_macaulayPow_of_lt {d : ℕ} (hd : 1 ≤ d) {a b : ℕ} (h : a < b) :
    Nat.macaulayPow d a < Nat.macaulayPow d b := by exact @_root_.P2MW.S_Nat_macaulayPow_lt_macaulayPow_of_lt.solution d hd a b h
