import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.FullRankExclusion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.IsotropyGeometry

open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.Support

def coordinateSigns : I3 → I3 → ℝ :=
  ![![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

def coordinateTurn (i : I3) : SO3 := by
  let T : Mat3 := Matrix.diagonal (coordinateSigns i)
  refine ⟨T, (Matrix.mem_specialOrthogonalGroup_iff).2 ⟨?_, ?_⟩⟩
  · apply (Matrix.mem_orthogonalGroup_iff' I3 ℝ).2
    ext r s
    fin_cases i <;> fin_cases r <;> fin_cases s <;>
      simp [T, coordinateSigns, Matrix.mul_apply, Fin.sum_univ_succ]
  · change (Matrix.diagonal (coordinateSigns i)).det = 1
    rw [Matrix.det_diagonal]
    fin_cases i <;> simp [coordinateSigns, Fin.prod_univ_succ]

end S3xS3.Trivial.IsotropyGeometry
