import Tengoku.SingularityCompleteLean.Singularity.FiniteEntranceIteration
import Tengoku.SingularityCompleteLean.Singularity.GeometricEntranceErrors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric conditions sufficient for the finite entrance iteration

The relative detour estimates in both orientations and a summable radius
schedule discharge the error hypotheses of the transfer argument. A finite
sequence of orbit balls and admissible endpoint sets with the stated properties
is constructed in the later CocompactAxisAncona module.
No existence of such a geometric sequence is assumed as an axiom.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A reversed geometric error schedule has total mass at most one half.
@isnad1 id=le.1h2v.s7.cb449cbe71e5 from=translated src=- shape=f117861f vocab=a7bdb361
-/
theorem finite_geometric_errors_le_half (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ n < N, ε n ≤ (1 / 4) * (1 / 2 : ℝ) ^ (N - 1 - n)) :
    ∑ n ∈ Finset.range N, ε n ≤ 1 / 2 := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, (1 / 4) * (1 / 2 : ℝ) ^ (N - 1 - n) :=
      Finset.sum_le_sum (fun n hn => hε n (Finset.mem_range.mp hn))
    _ = (1 / 4) * ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n := by
      rw [← Finset.mul_sum, Finset.sum_range_reflect]
    _ ≤ (1 / 4) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).sum_le_tsum (Finset.range N) (fun _ _ => by positivity)
    _ = 1 / 2 := by rw [tsum_geometric_two]; norm_num

/-- Radii separated backwards by at least log 2 give the required total loss.
@isnad1 id=le.1h2v.s6.e6c2c10b5163 from=translated src=- shape=1c3d919c vocab=fc162c39
-/
theorem finite_radius_errors_le_half (N : ℕ) (r : ℕ → ℝ)
    (hr : ∀ n < N, Real.log 4 + (N - 1 - n : ℕ) * Real.log 2 ≤ r n) :
    ∑ n ∈ Finset.range N, Real.exp (-r n) ≤ 1 / 2 := by
  apply finite_geometric_errors_le_half N
  intro n hn
  calc
    _ ≤ Real.exp (-(Real.log 4 + (N - 1 - n : ℕ) * Real.log 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (hr n hn))
    _ = (1 / 4) * (1 / 2 : ℝ) ^ (N - 1 - n) := by
      rw [neg_add, Real.exp_add, ← mul_neg, Real.exp_nat_mul,
        Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4),
        Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

end Singularity
