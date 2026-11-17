import Tengoku.FltAnthropic.Definitions.Def_FrobeniusDensity_PrimeSums
import Tengoku.FltAnthropic.P2M.Sol.S_FrobeniusDensity_primeSum_eq_degOneSum_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FrobeniusDensity_primeSum_eq_degOneSum_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.0h3v.s5.f7d74ca214d4 from=translated src=- shape=26693953 vocab=b3156205
-/
theorem FrobeniusDensity.primeSum_eq_degOneSum_add
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) (s : ℝ) :
    FrobeniusDensity.primeSum K s =
      FrobeniusDensity.degOneSum K S₀ s + FrobeniusDensity.cutSum K S₀ s +
      FrobeniusDensity.tailSum K s := by exact @_root_.P2MW.S_FrobeniusDensity_primeSum_eq_degOneSum_add.solution K _ _ S₀ s
