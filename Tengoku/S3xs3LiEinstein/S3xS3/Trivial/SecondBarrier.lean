import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.SwappedEuler

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.SecondBarrier

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.FactorSwap
open S3xS3.Trivial.FactorSwapFormulas
open S3xS3.Trivial.SwappedEuler
open S3xS3.Trivial.SwapNaturality

lemma strictBelowFour_diagonal_of_entries (s : I3 → ℝ)
    (hs : ∀ i, s i < 4) :
    S3xS3.Trivial.StrictBelowFour (Matrix.diagonal s) := by
  intro v hv
  have hn := normSq3_pos hv
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  simp [S3xS3.Trivial.quad3, S3xS3.Trivial.normSq3,
    Fin.sum_univ_succ] at hn ⊢
  have hn0 : 0 ≤ (4 - s 0) * v 0 ^ 2 :=
    mul_nonneg (sub_nonneg.mpr h0.le) (sq_nonneg _)
  have hn1 : 0 ≤ (4 - s 1) * v 1 ^ 2 :=
    mul_nonneg (sub_nonneg.mpr h1.le) (sq_nonneg _)
  have hn2 : 0 ≤ (4 - s 2) * v 2 ^ 2 :=
    mul_nonneg (sub_nonneg.mpr h2.le) (sq_nonneg _)
  by_cases hv0 : v 0 = 0
  · by_cases hv1 : v 1 = 0
    · have hv2 : v 2 ≠ 0 := by
        intro hv2
        apply hv
        funext i
        fin_cases i <;> assumption
      have hp2 : 0 < (4 - s 2) * v 2 ^ 2 :=
        mul_pos (sub_pos.mpr h2) (sq_pos_of_ne_zero hv2)
      nlinarith
    · have hp1 : 0 < (4 - s 1) * v 1 ^ 2 :=
        mul_pos (sub_pos.mpr h1) (sq_pos_of_ne_zero hv1)
      nlinarith
  · have hp0 : 0 < (4 - s 0) * v 0 ^ 2 :=
      mul_pos (sub_pos.mpr h0) (sq_pos_of_ne_zero hv0)
    nlinarith

noncomputable def barrierTransferMatrix {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) (t : ℝ) : Mat3 :=
  Real.sqrt t • (pdSqrt d.P * invBRoot m)

end S3xS3.Trivial.SecondBarrier
