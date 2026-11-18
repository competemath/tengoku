import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ModuliPoint
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine
theorem ModularCurve.natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq
    (N : ℕ) (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L]
    (W : WeierstrassCurve L) [W.IsElliptic] :
    Nat.card {x : ModuliPoint N L // ModuliPoint.j x = W.j}
      = Nat.card (Quot (fun (T T' : {T : W.toAffine.Point // addOrderOf T = N}) =>
          ∃ γ : VariableChange L, ∃ _ : γ • W = W, ∃ k : ℕ, k.Coprime N ∧
            HEq T'.1 (k • Point.vcInvFun γ W.toAffine T.1))) := by exact @_root_.P2MW.S_ModularCurve_natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq.solution N L _ _ _ W _
