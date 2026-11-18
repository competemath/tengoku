import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Tengoku.FltAnthropic.P2M.Sol.S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open WeierstrassCurve

universe u in

theorem WeierstrassCurve.cyclicQuotientJ_variableChange_eq
    {L : Type u} [Field L] [DecidableEq L] (C : VariableChange L) (E : WeierstrassCurve L)
    (H : AddSubgroup E.toAffine.Point) (H' : AddSubgroup (C • E).toAffine.Point)
    (hH' : ∀ P, P ∈ H' ↔ WeierstrassCurve.Affine.Point.vcFun C E P ∈ H)
    (N : ℕ) (hN : (N : L) ≠ 0) :
    (C • E).cyclicQuotientJ H' N = E.cyclicQuotientJ H N := by exact @_root_.P2MW.S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.solution L _ _ C E H H' hH' N hN
