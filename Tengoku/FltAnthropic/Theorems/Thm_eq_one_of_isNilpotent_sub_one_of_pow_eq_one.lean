import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_eq_one_of_isNilpotent_sub_one_of_pow_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_eq_one_of_isNilpotent_sub_one_of_pow_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

theorem _root_.Tengoku.FltAnthropic.eq_one_of_isNilpotent_sub_one_of_pow_eq_one
    {A : Type*} [Ring A] {u : A} (hu : IsNilpotent (u - 1))
    {m : ℕ} (hm : IsUnit (m : A)) (h : u ^ m = 1) :
    u = 1 := by exact @_root_.P2MW.S_eq_one_of_isNilpotent_sub_one_of_pow_eq_one.solution A _ u hu m hm h
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
