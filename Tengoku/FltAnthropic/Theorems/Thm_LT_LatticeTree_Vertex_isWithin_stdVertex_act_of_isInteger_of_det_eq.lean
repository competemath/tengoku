import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeBaseChange
import Tengoku.FltAnthropic.P2M.Sol.S_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open LT.LatticeTree

/--
@isnad1 id=iswithin.3h6v.s8.7e09f39141e6 from=translated src=- shape=90c1f5d9 vocab=78d0de2e
-/
theorem LT.LatticeTree.Vertex.isWithin_stdVertex_act_of_isInteger_of_det_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) k
      (LT.LatticeTree.stdVertex R K) (LT.LatticeTree.Vertex.act g (LT.LatticeTree.stdVertex R K)) := by exact @_root_.P2MW.S_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq.solution R K _ _ _ _ _ _ ϖ hϖ g hint k u hdet
