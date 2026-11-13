import Tengoku.LeanCommutator.PavingSeparation.PlanarEnergy
import Tengoku.Seed.Analysis.CStarAlgebra.Matrix
import Tengoku.Seed.LinearAlgebra.Matrix.IsDiag

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit bounds for the diagonal-commutator cost of flat matrices

The explicit planar energy bound controls every original-coordinate diagonal
commutator representation, both with square-normalized entries and after scaling
an arbitrary diagonal factor. All norms are Euclidean operator norms.
No optimality is claimed for the coefficients in these lower bounds.
-/

noncomputable section

namespace PavingSeparation.DiagonalCost

open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- The explicit bound is at least the simpler lower bound √k / 4.-/
theorem sqrt_k_lower_bound (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 < n) :
    Real.sqrt (k : ℝ) / 4 ≤
      Real.sqrt ((((3 : ℝ) * k - 1) * n + 1) / (32 * ((n : ℝ) - 1))) := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hratio : (k : ℝ) / 16 ≤
      (((3 : ℝ) * k - 1) * n + 1) / (32 * ((n : ℝ) - 1)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 32)
      (by linarith : 0 < (n : ℝ) - 1))).mpr
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) - 1 by linarith) (Nat.cast_nonneg n)]
  have hs := Real.sqrt_le_sqrt hratio
  norm_num [Real.sqrt_div (Nat.cast_nonneg k)] at hs ⊢
  exact hs

end PavingSeparation.DiagonalCost
