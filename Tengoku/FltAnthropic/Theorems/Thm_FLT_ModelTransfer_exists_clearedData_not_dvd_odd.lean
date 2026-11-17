import Tengoku.FltAnthropic.Definitions.Def_ModelTransfer_ClearedData
import Tengoku.FltAnthropic.P2M.Sol.S_FLT_ModelTransfer_exists_clearedData_not_dvd_odd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FLT_ModelTransfer_exists_clearedData_not_dvd_odd.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open WeierstrassCurve
namespace FLT.ModelTransfer
/--
@isnad1 id=ex.5h4v.s6.903e1ac2453e from=translated src=- shape=3a745abe vocab=b55e545e
-/
theorem exists_clearedData_not_dvd_odd {V W : WeierstrassCurve ℤ} {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    ∃ D : FLT.ModelTransfer.ClearedData C, ¬ q ∣ D.N := by exact @_root_.P2MW.S_FLT_ModelTransfer_exists_clearedData_not_dvd_odd.solution V W C q hq hq2 hC hV hW
end FLT.ModelTransfer
