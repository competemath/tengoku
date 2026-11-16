import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_HeckeEigensystem
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_satakePow_add_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_satakePow_add_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open IsDedekindDomain NumberField AutomorphicForm
/--
@isnad1 id=eq.0h4v.s6.1331cf859814 from=translated src=- shape=e6e529e8 vocab=39e41ec2
-/
theorem AutomorphicForm.satakePow_add_pow {R : Type*} [CommRing R] (α β : R) :
    ∀ n : ℕ, satakePow n (α + β) (α * β) = α ^ n + β ^ n := by exact @_root_.P2MW.S_AutomorphicForm_satakePow_add_pow.solution R _ α β
