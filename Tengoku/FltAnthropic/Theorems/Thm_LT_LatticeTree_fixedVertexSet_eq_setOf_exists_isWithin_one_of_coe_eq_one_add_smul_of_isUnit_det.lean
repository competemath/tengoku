import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeBaseChange
import Tengoku.FltAnthropic.P2M.Sol.S_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_smul_of_isUnit_det

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_smul_of_isUnit_det.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem LT.LatticeTree.fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_smul_of_isUnit_det
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (Y : Matrix (Fin 2) (Fin 2) R) (b : R)
    (hdet : IsUnit (b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).det)
    (g g' : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K b • 1 + Y.map (algebraMap R K))
    (hg' : (g' : Matrix (Fin 2) (Fin 2) K) = 1 + algebraMap R K ϖ • Y.map (algebraMap R K)) :
    LT.LatticeTree.fixedVertexSet (R := R) g' =
      {x | ∃ y ∈ LT.LatticeTree.fixedVertexSet (R := R) g,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 y x} := by exact @_root_.P2MW.S_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_smul_of_isUnit_det.solution R K _ _ _ _ _ _ ϖ hϖ Y b hdet g g' hg hg'
