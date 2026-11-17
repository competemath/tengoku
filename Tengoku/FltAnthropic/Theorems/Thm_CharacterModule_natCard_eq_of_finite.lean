import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_CharacterModule_natCard_eq_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CharacterModule_natCard_eq_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.0h1v.s4.2dbc67dd7724 from=translated src=- shape=210878d7 vocab=f37ffda3
-/
theorem CharacterModule.natCard_eq_of_finite (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card (CharacterModule M) = Nat.card M := by exact @_root_.P2MW.S_CharacterModule_natCard_eq_of_finite.solution M _ _
