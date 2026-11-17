import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRep_mem_ratLocalizedAt_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRep_mem_ratLocalizedAt_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=iff.1h2v.s5.0bdd73cb1a52 from=translated src=- shape=c36e0ae1 vocab=665e5dc6
-/
theorem GaloisRep.mem_ratLocalizedAt_iff
    {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ GaloisRep.ratLocalizedAt p ↔ ¬ p ∣ q.den := by exact @_root_.P2MW.S_GaloisRep_mem_ratLocalizedAt_iff.solution p hp q
