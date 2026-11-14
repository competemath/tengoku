import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Strict bounds for the odd-power logarithm series in section 3 and Appendix A. -/

namespace PiIrrationality

noncomputable def oddLogTerm (z : ℝ) (q : ℕ) : ℝ :=
  2 * (1 / (2 * (q : ℝ) + 1)) * z ^ (2 * q + 1)

noncomputable def oddLogPartialSum (z : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.range N, oddLogTerm z q

noncomputable def oddLogTailBound (z : ℝ) (N : ℕ) : ℝ :=
  2 * z ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - z ^ 2))

theorem oddLogPartialSum_eq (z : ℝ) (N : ℕ) :
    oddLogPartialSum z N = 2 * ∑ q ∈ Finset.range N, z ^ (2 * q + 1) / (2 * (q : ℝ) + 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  dsimp [oddLogTerm]
  ring

theorem oddLogTailBound_lt {z w : ℝ} (hz : 0 < z) (hzw : z < w) (hw : w < 1) (N : ℕ) :
    oddLogTailBound z N < oddLogTailBound w N := by
  have hw0 := hz.trans hzw
  have hzsq : z ^ 2 < w ^ 2 := by nlinarith
  have hwsq : w ^ 2 < 1 := by nlinarith
  have hdz : 0 < (2 * (N : ℝ) + 1) * (1 - z ^ 2) :=
    mul_pos (by positivity) (sub_pos.mpr (hzsq.trans hwsq))
  unfold oddLogTailBound
  calc
    2 * z ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - z ^ 2)) ≤
        2 * w ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - z ^ 2)) := by
      gcongr
    _ < 2 * w ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - w ^ 2)) := by
      apply div_lt_div_of_pos_left (by positivity) (by positivity)
      exact mul_lt_mul_of_pos_left (sub_lt_sub_left hzsq 1) (by positivity)

theorem oddLogTerm_hasSum {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (oddLogTerm z) (Real.log ((1 + z) / (1 - z))) := by
  rw [Real.log_div (by linarith) (by linarith)]
  exact Real.hasSum_log_sub_log_of_abs_lt_one (by rwa [abs_of_nonneg hz0])

theorem oddLogTerm_pos {z : ℝ} (hz : 0 < z) (q : ℕ) : 0 < oddLogTerm z q := by
  unfold oddLogTerm
  positivity

theorem oddLogTerm_shift_le_geometric {z : ℝ} (hz : 0 < z) (N q : ℕ) :
    oddLogTerm z (q + N) ≤
      (2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) * (z ^ 2) ^ q := by
  have heq : oddLogTerm z (q + N) =
      2 * z ^ (2 * N + 1) * (z ^ 2) ^ q / (2 * ((q : ℝ) + N) + 1) := by
    unfold oddLogTerm
    rw [show 2 * (q + N) + 1 = (2 * N + 1) + 2 * q by omega, pow_add, pow_mul]
    push_cast
    ring
  rw [heq, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have := Nat.cast_nonneg (α := ℝ) q
  linarith

theorem oddLogTerm_shift_lt_geometric {z : ℝ} (hz : 0 < z) (N : ℕ) :
    oddLogTerm z (1 + N) <
      (2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1)) * (z ^ 2) ^ 1 := by
  have heq : oddLogTerm z (1 + N) =
      2 * z ^ (2 * N + 1) * (z ^ 2) ^ 1 / (2 * (1 + (N : ℝ)) + 1) := by
    unfold oddLogTerm
    rw [show 2 * (1 + N) + 1 = (2 * N + 1) + 2 * 1 by omega, pow_add, pow_mul]
    push_cast
    ring
  rw [heq, div_mul_eq_mul_div]
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  linarith

theorem oddLogSeries_tail_bounds {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (N : ℕ) :
    0 < Real.log ((1 + z) / (1 - z)) - oddLogPartialSum z N ∧
      Real.log ((1 + z) / (1 - z)) - oddLogPartialSum z N < oddLogTailBound z N := by
  have hs := (oddLogTerm_hasSum hz0.le hz1).summable
  have hsN := (summable_nat_add_iff N).mpr hs
  have heq : Real.log ((1 + z) / (1 - z)) - oddLogPartialSum z N =
      ∑' q : ℕ, oddLogTerm z (q + N) := by
    have h := hs.sum_add_tsum_nat_add N
    rw [(oddLogTerm_hasSum hz0.le hz1).tsum_eq] at h
    dsimp [oddLogPartialSum]
    linarith
  rw [heq]
  constructor
  · exact hsN.tsum_pos (fun q => (oddLogTerm_pos hz0 (q + N)).le) 0
      (oddLogTerm_pos hz0 (0 + N))
  · have hzsq : ‖z ^ 2‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
      nlinarith
    have hg := (hasSum_geometric_of_norm_lt_one hzsq).mul_left
      (2 * z ^ (2 * N + 1) / (2 * (N : ℝ) + 1))
    have hlt := hsN.tsum_lt_tsum (oddLogTerm_shift_le_geometric hz0 N)
      (oddLogTerm_shift_lt_geometric hz0 N) hg.summable
    rw [hg.tsum_eq] at hlt
    simpa only [oddLogTailBound, div_eq_mul_inv, mul_inv_rev, mul_assoc,
      mul_left_comm, mul_comm] using hlt

end PiIrrationality
