import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_free_and_finrank_add_eq_of_isCompl

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_free_and_finrank_add_eq_of_isCompl.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem IsLocalRing.free_and_finrank_add_eq_of_isCompl
    {C : Type} [CommRing C] [IsLocalRing C] {N : Type} [AddCommGroup N] [Module C N]
    [Module.Finite C N] [Module.Free C N] (N0 N1 : Submodule C N) (h : IsCompl N0 N1) :
    Module.Free C N0 ∧ Module.Finite C N0 ∧ Module.Free C N1 ∧ Module.Finite C N1 ∧
      Module.finrank C N0 + Module.finrank C N1 = Module.finrank C N := by exact @_root_.P2MW.S_IsLocalRing_free_and_finrank_add_eq_of_isCompl.solution C _ _ N _ _ _ _ N0 N1 h
