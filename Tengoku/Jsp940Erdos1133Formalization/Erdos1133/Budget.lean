import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
namespace Erdos1133

/-- One parameter controls both the degree surplus and the allowed errors.-/
def obstructionEpsilon (k : ℕ) : ℝ := 1 / (8 * (k : ℝ)^2)

theorem obstructionEpsilon_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < obstructionEpsilon k := by
  unfold obstructionEpsilon
  have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  positivity

theorem obstructionEpsilon_lt_one {k : ℕ} (hk : 2 ≤ k) :
    obstructionEpsilon k < 1 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold obstructionEpsilon
  rw [div_lt_one (by positivity : (0 : ℝ) < 8 * (k : ℝ)^2)]
  nlinarith

/-- The exact elementary estimate used after partitioning the angular interval.-/
theorem robust_group_budget {k n q : ℕ} (hk : 2 ≤ k) (hn : 4*k^2 ≤ n)
    (hgroup : (n : ℝ) / k - ((1 + obstructionEpsilon k) * n) / (k + 1) - 1 ≤ q) :
    obstructionEpsilon k * n < q := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (4 : ℝ) * (k : ℝ)^2 ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have heq : (n : ℝ) / k - ((1 + obstructionEpsilon k) * n) / (k + 1) - 1 -
      obstructionEpsilon k * n =
      (n : ℝ) * (7*(k : ℝ)-2) / (8*(k : ℝ)^2*((k : ℝ)+1)) - 1 := by
    unfold obstructionEpsilon
    field_simp
    ring
  have hcoef : (1 : ℝ) / (2*(k : ℝ)^2) ≤
      (7*(k : ℝ)-2) / (8*(k : ℝ)^2*((k : ℝ)+1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_pos_of_pos hk0]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcoef hn0
  have hlarge : (2 : ℝ) ≤ (n : ℝ) / (2*(k : ℝ)^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have he : (1 : ℝ) ≤ (n : ℝ) / k -
      ((1 + obstructionEpsilon k) * n) / (k + 1) - 1 - obstructionEpsilon k * n := by
    rw [heq]
    simp only [← mul_div_assoc, mul_one] at hmul
    linarith
  linarith

end Erdos1133
