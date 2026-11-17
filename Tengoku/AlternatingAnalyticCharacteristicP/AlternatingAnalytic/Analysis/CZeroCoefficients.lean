import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.FiniteWordGrouping
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.CZeroCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting homogeneous diagonals on c₀

Let `p` be a continuous multilinear map on `C₀(I, K)`, `I` discrete, with values in an
ultrametric space `Z`, whose diagonal lies in a complete submodule `W`. Then some continuous
multilinear map into `W` has the same diagonal and norm at most `‖p‖`. Its coefficients are
the grouped coefficients of `FiniteWord`. This is the coefficient lift of Theorem 4.5(1).
-/

noncomputable section

open scoped Topology ZeroAtInfty BigOperators
open Filter

namespace CZero

variable {I K Z : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NontriviallyNormedField K] [NormedAddCommGroup Z] [NormedSpace K Z]
  [IsUltrametricDist Z] {n : ℕ}

/-- Grouping distinct coordinate words preserves the operator-norm bound.
@isnad1 id=le.0h6v.s10.97f1cb6c85ee from=translated src=- shape=411103b3 vocab=52472625
-/
theorem norm_groupedCoefficient_le
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (a : Fin n → I) :
    ‖FiniteWord.groupedCoefficient p.toMultilinearMap (coordinate (K := K)) a‖ ≤ ‖p‖ := by
  classical
  by_cases ha : FiniteWord.wordRepresentative a = a
  · rw [FiniteWord.groupedCoefficient_of_representative _ _ ha]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg p)
    intro u hu
    apply p.unit_le_opNorm
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun r => norm_coordinate_le (u r))
  · rw [FiniteWord.groupedCoefficient_of_not_representative _ _ ha, norm_zero]
    exact norm_nonneg p

variable (W : Submodule K Z) [CompleteSpace W]

end CZero
