import Tengoku.Pi2Lean.Row12.Convergence
import Tengoku.Seed.Data.Nat.Choose.Cast

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Row12

noncomputable def weightedKernel (r : ℝ) : ℝ :=
  (9 + 640 * r + 415 * r ^ 2) / (1 - r) ^ 3

/--
@isnad1 id=hassum.1h1v.s5.212a296adb76 from=translated src=- shape=eed83c29 vocab=2e9db18d
-/
theorem weighted_geometric_hasSum {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ => weight n * r ^ n) (weightedKernel r) := by
  have hn : ‖r‖ < 1 := hr
  have hchoose := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hn).mul_left (1064 : ℝ)
  have hlinear := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left (1470 : ℝ)
  have hzero := (hasSum_geometric_of_norm_lt_one hn).mul_left (1055 : ℝ)
  have hden : 1 - r ≠ 0 := by
    have : r < 1 := (abs_lt.mp hr).2
    linarith
  have hsum := (hchoose.sub hlinear).sub hzero
  have hfun : (fun n : ℕ => weight n * r ^ n) =
      (fun n : ℕ => 1064 * ((↑((n + 2).choose 2) : ℝ) * r ^ n) -
        1470 * ((n : ℝ) * r ^ n) - 1055 * r ^ n) := by
    funext n
    rw [Nat.cast_choose_two]
    simp only [Nat.cast_add, Nat.cast_ofNat, weight]
    ring
  have hval : weightedKernel r =
      1064 * (1 / (1 - r) ^ (2 + 1)) - 1470 * (r / (1 - r) ^ 2) -
        1055 * (1 - r)⁻¹ := by
    unfold weightedKernel
    field_simp [hden]
    ring
  rw [← hfun, ← hval] at hsum
  exact hsum

/--
@isnad1 id=summable.1h1v.s5.8c57dc157f3e from=translated src=- shape=377dcba5 vocab=26bb6e29
-/
theorem weighted_geometric_summable {r : ℝ} (hr : |r| < 1) :
    Summable (fun n : ℕ => weight n * r ^ n) :=
  (weighted_geometric_hasSum hr).summable

/--
@isnad1 id=eq.1h1v.s5.1390b1f6bfa7 from=translated src=- shape=b37ebe8f vocab=b25e81d1
-/
theorem weighted_geometric_tsum {r : ℝ} (hr : |r| < 1) :
    (∑' n : ℕ, weight n * r ^ n) = weightedKernel r :=
  (weighted_geometric_hasSum hr).tsum_eq

end Row12
