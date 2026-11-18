import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_FunctionField
import Tengoku.FltAnthropic.P2M.Sol.S_DrinfeldCurve_exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DrinfeldCurve_exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open DrinfeldCurve

theorem DrinfeldCurve.exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv
    (q : ℕ) [Fact q.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (k' : Type) [Field k'] [Algebra (GaloisField q 2) k'] [IsDomain (DrinfeldCurve.CoordRing q k')]
    (e : k ≃ₐ[GaloisField q 2] k') :
    ∃ φ : drinfeldFunctionField q k ≃+* drinfeldFunctionField q k',
      (∀ a : k, φ (algebraMap k (drinfeldFunctionField q k) a) = algebraMap k' (drinfeldFunctionField q k') (e a)) ∧
      φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (DrinfeldCurve.x q k)) =
        algebraMap (CoordRing q k') (drinfeldFunctionField q k') (DrinfeldCurve.x q k') ∧
      φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (DrinfeldCurve.y q k)) =
        algebraMap (CoordRing q k') (drinfeldFunctionField q k') (DrinfeldCurve.y q k') ∧
      (∀ (h : hSubgroup q) (f : drinfeldFunctionField q k),
        φ (hFunctionFieldAction q k h f) = hFunctionFieldAction q k' h (φ f)) := by exact @_root_.P2MW.S_DrinfeldCurve_exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv.solution q _ k _ _ _ k' _ _ _ e
