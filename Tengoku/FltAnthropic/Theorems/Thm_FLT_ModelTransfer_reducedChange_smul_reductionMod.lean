import Tengoku.FltAnthropic.Definitions.Def_ModelTransfer_ClearedData
import Tengoku.FltAnthropic.P2M.Sol.S_FLT_ModelTransfer_reducedChange_smul_reductionMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FLT_ModelTransfer_reducedChange_smul_reductionMod.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open WeierstrassCurve
namespace FLT.ModelTransfer
/--
@isnad1 id=eq.2h5v.s6.7ec7fd43c8a1 from=translated src=- shape=af24b03d vocab=968469e3
-/
theorem reducedChange_smul_reductionMod {V W : WeierstrassCurve ℤ} {C : WeierstrassCurve.VariableChange ℚ}
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (D : FLT.ModelTransfer.ClearedData C) {q : ℕ} [Fact q.Prime] (hq : ¬ q ∣ D.N) :
    (FLT.ModelTransfer.reducedChange D hq) • (V.reductionMod q) = W.reductionMod q := by exact @_root_.P2MW.S_FLT_ModelTransfer_reducedChange_smul_reductionMod.solution V W C hC D q _ hq
end FLT.ModelTransfer
