import Tengoku.Seed.RingTheory.DiscreteValuationRing.Basic
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRep_isDiscreteValuationRing_ratLocalizedAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem GaloisRep.isDiscreteValuationRing_ratLocalizedAt (p : ℕ) (hp : p.Prime) :
    IsDiscreteValuationRing (GaloisRep.ratLocalizedAt p) := by exact @_root_.P2MW.S_GaloisRep_isDiscreteValuationRing_ratLocalizedAt.solution p hp
