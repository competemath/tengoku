import Tengoku.Seed.NumberTheory.Bernoulli
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact rational verification of the Bernoulli numbers listed in (3.17). -/

namespace PiIrrationality

def paperBernoulli (n : ℕ) : ℚ :=
  ([1, -1 / 2, 1 / 6, 0, -1 / 30, 0, 1 / 42, 0, -1 / 30, 0, 5 / 66, 0,
    -691 / 2730, 0, 7 / 6, 0, -3617 / 510, 0, 43867 / 798, 0, -174611 / 330, 0,
    854513 / 138, 0, -236364091 / 2730] : List ℚ).getD n 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Check all 24 finite recurrences using kernel-checked rational arithmetic.
theorem paperBernoulli_recurrence :
    ∀ n ∈ Finset.Icc 1 24, ∑ k ∈ Finset.range (n + 1),
      ((n + 1).choose k : ℚ) * paperBernoulli k = 0 := by
  intro n hn
  obtain ⟨hn1, hn24⟩ := Finset.mem_Icc.mp hn
  interval_cases n <;> norm_num [paperBernoulli, Finset.sum_range_succ, Nat.choose]

theorem bernoulli_eq_paperBernoulli {n : ℕ} (hn : n ≤ 24) : bernoulli n = paperBernoulli n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      norm_num [paperBernoulli]
    have hnat := sum_bernoulli (n + 1)
    have hrat := paperBernoulli_recurrence n (Finset.mem_Icc.mpr ⟨by omega, hn⟩)
    rw [ite_eq_right (by omega : n + 1 ≠ 1), Finset.sum_range_succ] at hnat
    rw [Finset.sum_range_succ] at hrat
    have he : (∑ k ∈ Finset.range n, ((n + 1).choose k : ℚ) * bernoulli k) =
        ∑ k ∈ Finset.range n, ((n + 1).choose k : ℚ) * paperBernoulli k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [ih k hk' (by omega)]
    rw [he] at hnat
    have hc : ((n + 1).choose n : ℚ) ≠ 0 := by
      rw [Nat.choose_succ_self_right]
      positivity
    apply mul_left_cancel₀ hc
    linarith

theorem bernoulli_twenty_four : bernoulli 24 = -(236364091 : ℚ) / 2730 := by
  rw [bernoulli_eq_paperBernoulli (by norm_num)]
  norm_num [paperBernoulli]

end PiIrrationality
