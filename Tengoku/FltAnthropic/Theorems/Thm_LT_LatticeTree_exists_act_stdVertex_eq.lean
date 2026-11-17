import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeBaseChange
import Tengoku.FltAnthropic.P2M.Sol.S_LT_LatticeTree_exists_act_stdVertex_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_LatticeTree_exists_act_stdVertex_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem LT.LatticeTree.exists_act_stdVertex_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : LT.LatticeTree.Vertex R K) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K,
      LT.LatticeTree.Vertex.act g (LT.LatticeTree.stdVertex R K) = v := by exact @_root_.P2MW.S_LT_LatticeTree_exists_act_stdVertex_eq.solution R K _ _ _ _ _ _ v
