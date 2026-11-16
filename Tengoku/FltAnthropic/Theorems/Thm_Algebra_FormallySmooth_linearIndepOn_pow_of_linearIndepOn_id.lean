import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=linearin.2h4v.s7.b4f104510245 from=translated src=- shape=baddcd99 vocab=543b1c29
-/
theorem Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.FormallySmooth k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) := by exact @_root_.P2MW.S_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id.solution k K _ _ _ _ p hp _ s hs
