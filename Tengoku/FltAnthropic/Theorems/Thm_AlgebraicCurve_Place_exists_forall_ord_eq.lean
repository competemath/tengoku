import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_exists_forall_ord_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_exists_forall_ord_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve
/--
@isnad1 id=ex.0h4v.s6.248fae9d6630 from=translated src=- shape=4a1e48c2 vocab=49cc900f
-/
theorem AlgebraicCurve.Place.exists_forall_ord_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (T : Finset (Place K F)) (n : Place K F → ℤ) :
    ∃ f : F, f ≠ 0 ∧ ∀ v ∈ T, v.ord f = n v := by exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_forall_ord_eq.solution K F _ _ _ T n
