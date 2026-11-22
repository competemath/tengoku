import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Submodule_eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Submodule_eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) [IsAdicComplete I A] [IsHausdorff I M]
    (N : Submodule A M) (hN : N.FG) (h : N ⊔ I • ⊤ = ⊤) : N = ⊤ := by exact @_root_.P2MW.S_Submodule_eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top.solution A M _ _ _ I _ _ N hN h
