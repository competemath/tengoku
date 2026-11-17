import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeBaseChange
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Tengoku.FltAnthropic.Theorems.Thm_LT_LatticeTree_Vertex_isWithin_iff_dist_le
import Tengoku.FltAnthropic.Theorems.Thm_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq

set_option autoImplicit false

open LT.LatticeTree

/--
@isnad1 id=le.3h6v.s9.02e14a459303 from=translated src=- shape=45b7fbc7 vocab=2d6ddd49
-/
theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    (CerednikDrinfeld.BruhatTits.tree R K).dist (LT.LatticeTree.stdVertex R K)
      (g • LT.LatticeTree.stdVertex R K) ≤ k := by
  rw [← LT.LatticeTree.Vertex.isWithin_iff_dist_le R K ϖ hϖ]
  exact LT.LatticeTree.Vertex.isWithin_stdVertex_act_of_isInteger_of_det_eq R K ϖ hϖ g hint k u hdet
