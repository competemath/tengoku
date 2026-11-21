import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_GluedPic0
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.1h3v.s14.12a33f3145d5 from=translated src=- shape=0f421509 vocab=309ff463
-/
theorem AlgebraicCurve.GluedPic0.ker_toPic0Pair_eq_range_nodeUnit {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Finset (AlgebraicCurve.Place K F × AlgebraicCurve.Place K F))
    (hrat : ∀ s : ↥S,
      Function.Surjective (algebraMap K ((s : AlgebraicCurve.Place K F × AlgebraicCurve.Place K F).1.ResidueField)) ∧
        Function.Surjective (algebraMap K ((s : AlgebraicCurve.Place K F × AlgebraicCurve.Place K F).2.ResidueField))) :
    (AlgebraicCurve.GluedPic0.toPic0Pair S).ker = (AlgebraicCurve.GluedPic0.nodeUnit S).range := by exact @_root_.P2MW.S_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit.solution K F _ _ _ S hrat
