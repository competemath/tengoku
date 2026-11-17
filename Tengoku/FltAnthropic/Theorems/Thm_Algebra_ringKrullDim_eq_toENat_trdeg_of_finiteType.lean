import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v

theorem Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) := by exact @_root_.P2MW.S_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType.solution k A _ _ _ _ _
