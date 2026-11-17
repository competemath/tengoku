import Tengoku.Seed.RingTheory.HopfAlgebra.Basic
import Tengoku.Seed.RingTheory.FiniteType
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=isreduce.0h2v.s6.7b805ec31840 from=translated src=- shape=1b367238 vocab=2148d0d5
-/
theorem HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by exact @_root_.P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero.solution K _ _ _ A _ _ _
