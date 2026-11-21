import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspidalType_IsCuspidalOfType
import Tengoku.FltAnthropic.P2M.Sol.S_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

local notation α "^+" M:51 => FixedPoints.addSubgroup M α

set_option autoImplicit false

open Polynomial CuspidalType

/--
@isnad1 id=ex.1h3v.s8.092aacdfcc8a from=translated src=- shape=cd9f83db vocab=bc5582bf
-/
theorem CuspidalType.exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
    (q : ℕ) [Fact q.Prime]
    (g : GL2 q) (x : ZMod q)
    (hx : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x) :
    ∃ h : GL2 q, ((h * g * h⁻¹ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := by exact @_root_.P2MW.S_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly.solution q _ g x hx
