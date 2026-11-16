import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRep_isLocalization_ratLocalizedAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRep_isLocalization_ratLocalizedAt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=atprime.1h1v.s7.1ef829d05ee6 from=translated src=- shape=51bc8d3a vocab=7a910803
-/
theorem GaloisRep.isLocalization_ratLocalizedAt
    {p : ℕ} (hp : p.Prime) [(Ideal.span {(p : ℤ)}).IsPrime] :
    IsLocalization.AtPrime (GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)}) := by exact @_root_.P2MW.S_GaloisRep_isLocalization_ratLocalizedAt.solution p hp _
