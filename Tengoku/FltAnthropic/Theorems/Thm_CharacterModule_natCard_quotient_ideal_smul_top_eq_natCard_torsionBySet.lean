import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem CharacterModule.natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet
    (A : Type*) [CommRing A] (G : Type*) [AddCommGroup G] [Module A G]
    (s : Set A) (hs : s.Finite) (hfin : Finite ↥(Submodule.torsionBySet A G s)) :
    Nat.card (CharacterModule G ⧸ (Ideal.span s • (⊤ : Submodule A (CharacterModule G))))
      = Nat.card ↥(Submodule.torsionBySet A G s) := by exact @_root_.P2MW.S_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet.solution A _ G _ _ s hs hfin
