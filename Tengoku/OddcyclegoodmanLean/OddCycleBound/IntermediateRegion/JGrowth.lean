import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv
import Tengoku.Seed.Analysis.Convex.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion

open Real

theorem log_one_sub_le_neg {s : ℝ} (hs : s < 1) : Real.log (1 - s) ≤ -s := by
  have h : Real.log (1 - s) ≤ (1 - s) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  linarith [h]

def LN (N x : ℝ) : ℝ :=
  (2 / N - 2 / N ^ 2) + (-2 * x - x ^ 2 - x ^ 4 / (1 - x) - x ^ 6 / 2)
    + (3 * N / 4 - 1) * (x ^ 2 - x ^ 4 / 2 + x ^ 2 / N)

private def Rpoly (N x : ℝ) : ℝ :=
  576 * N ^ 3 * x ^ 5 - 576 * N ^ 3 * x ^ 4 - 1152 * N ^ 3 * x ^ 3 + 1152 * N ^ 3 * x ^ 2
    + 768 * N ^ 2 * x ^ 7 - 768 * N ^ 2 * x ^ 6 - 768 * N ^ 2 * x ^ 5 - 768 * N ^ 2 * x ^ 4
    + 1920 * N ^ 2 * x ^ 3 + 1152 * N ^ 2 * x ^ 2 - 3072 * N ^ 2 * x + 1536 * N * x ^ 3
    - 1536 * N * x ^ 2 - 3072 * N * x + 3072 * N + 3072 * x - 3072

noncomputable def KN (N x : ℝ) : ℝ :=
  (N + 2) / N * (1 - x) ^ 2 * (1 + x ^ 3) * (1 + x ^ 2) ^ (3 * N / 4 - 1)

private noncomputable def flb (N : ℝ) : ℝ :=
  (N + 2) / N * (4 * (21 / 25) ^ 4 / N ^ 2) * (159 / 100) * (17 / 10) ^ (3 * N / 4 - 1)

private def PNf (N x : ℝ) : ℝ :=
  3 * N * x ^ 5 - 3 * N * x ^ 4 + 3 * N * x ^ 2 - 3 * N * x + 6 * x ^ 5 - 2 * x ^ 4 + 10 * x ^ 3
    - 6 * x ^ 2 + 4 * x + 4

private def PNf' (N x : ℝ) : ℝ :=
  15 * N * x ^ 4 - 12 * N * x ^ 3 + 6 * N * x - 3 * N + 30 * x ^ 4 - 8 * x ^ 3 + 30 * x ^ 2 - 12 * x + 4

private noncomputable def Gf (N y : ℝ) : ℝ :=
  Real.log ((N + 2) / N) + 2 * Real.log (1 - y) + Real.log (1 + y ^ 3)
    + (3 * N / 4 - 1) * Real.log (1 + y ^ 2)

end OddCycleBound.IntermediateRegion
