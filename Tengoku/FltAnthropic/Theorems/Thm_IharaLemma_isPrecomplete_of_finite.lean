import Tengoku.Seed.RingTheory.AdicCompletion.Basic
import Tengoku.Seed.RingTheory.Finiteness.Defs
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_isPrecomplete_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_isPrecomplete_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=isprecom.0h3v.s6.d5bd06a9e8b4 from=translated src=- shape=ca941a41 vocab=3c050046
-/
theorem IharaLemma.isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by exact @_root_.P2MW.S_IharaLemma_isPrecomplete_of_finite.solution R _ I _ M _ _ _
