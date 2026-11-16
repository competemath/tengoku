import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Defs
import Tengoku.Seed.RingTheory.Algebraic.Defs
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=finitedi.1h4v.s8.0941a67396c8 from=translated src=- shape=a3aa05a1 vocab=64ffeb68
-/
theorem AlgebraicCurve.finiteDimensional_adjoin_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by exact @_root_.P2MW.S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.solution K F _ _ _ x _ t ht
