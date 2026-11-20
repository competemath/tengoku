import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.FactorSwap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.FactorSwapFormulas

open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.FactorSwap

noncomputable def swapDetRoot (m : I3 → ℝ) : ℝ := (rootB m).det

noncomputable def swappedPClosed {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) : Mat3 :=
  (swapDetRoot m)⁻¹ •
    (pdSqrt d.Q * (rootB m * rootB m) * pdSqrt d.Q)

noncomputable def swappedQClosed {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) : Mat3 :=
  swapDetRoot m •
    (pdSqrt d.P * (invBRoot m * invBRoot m) * pdSqrt d.P)

@[simp] lemma swapGraphData_P {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).P = swappedP m d.E d.E_pos := rfl

@[simp] lemma swapGraphData_Q {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).Q = swappedQ m d.D d.D_pos := rfl

@[simp] lemma swapGraphData_M {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).M =
      swappedM m d.D d.E d.D_pos d.E_pos := rfl

end S3xS3.Trivial.FactorSwapFormulas
