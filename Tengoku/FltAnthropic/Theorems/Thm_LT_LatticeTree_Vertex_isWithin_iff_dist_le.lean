import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeBaseChange
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Tengoku.FltAnthropic.P2M.Sol.S_LT_LatticeTree_Vertex_isWithin_iff_dist_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_LatticeTree_Vertex_isWithin_iff_dist_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open LT.LatticeTree

theorem LT.LatticeTree.Vertex.isWithin_iff_dist_le
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) (n : ℕ) (v w : LT.LatticeTree.Vertex R K) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w ↔
      (CerednikDrinfeld.BruhatTits.tree R K).dist v w ≤ n := by exact @_root_.P2MW.S_LT_LatticeTree_Vertex_isWithin_iff_dist_le.solution R K _ _ _ _ _ _ ϖ hϖ n v w
