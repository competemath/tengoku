import Tengoku.Piirrationalitymeasure.Formalization.PeriodErrorSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A uniform tail estimate for a summable sequence bounded by inverse squares. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem hasSum_inverse_square_tail {f : ℕ → ℝ} {S : ℝ} (hs : HasSum f S)
    (hf : ∀ k : ℕ, 0 < k → |f k| ≤ 1 / (k : ℝ) ^ 2)
    {N : ℕ} (hN : 0 < N) :
    |S - ∑ k ∈ Finset.range N, f k| ≤ 2 / (N : ℝ) := by
  have hNs : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN := (summable_nat_add_iff N).mpr hs.summable
  have hbound (M : ℕ) : |∑ k ∈ Finset.range M, f (k + N)| ≤ 2 / (N : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range M, |f (k + N)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range M,
          (2 / ((k + N : ℕ) : ℝ) - 2 / (((k + N : ℕ) : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k _
        apply (hf (k + N) (by omega)).trans
        exact inverse_square_le_telescope (by exact_mod_cast (show 1 ≤ k + N by omega))
      _ = 2 / (N : ℝ) - 2 / ((M + N : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.zero_add, Nat.add_assoc, add_assoc,
          Nat.add_comm 1 N] using
          Finset.sum_range_sub' (fun k : ℕ => 2 / ((k + N : ℕ) : ℝ)) M
      _ ≤ 2 / (N : ℝ) := by
        have h : 0 ≤ 2 / ((M + N : ℕ) : ℝ) := by positivity
        linarith
  have ht : |∑' k : ℕ, f (k + N)| ≤ 2 / (N : ℝ) :=
    le_of_tendsto hsN.hasSum.tendsto_sum_nat.abs (Eventually.of_forall hbound)
  have he := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at he
  have he' : S - ∑ k ∈ Finset.range N, f k = ∑' k : ℕ, f (k + N) := by linarith
  rwa [he']

end PiIrrationality
