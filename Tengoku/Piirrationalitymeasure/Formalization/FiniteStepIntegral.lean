import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact integral and variation formulas for finite step functions. -/

namespace PiIrrationality

open MeasureTheory Set

theorem finite_step_integral (e eps : ℕ → ℝ) (f : ℝ → ℝ) (n : ℕ)
    (he : ∀ k < n, e k ≤ e (k + 1))
    (hf : ∀ k < n, ∀ x ∈ Ioo (e k) (e (k + 1)), f x = eps k) :
    (∫ x in e 0..e n, f x) = ∑ k ∈ Finset.range n, eps k * (e (k + 1) - e k) := by
  have hi : ∀ k < n, IntervalIntegrable f volume (e k) (e (k + 1)) := by
    intro k hk
    apply (intervalIntegrable_congr_uIoo (f := f) (g := fun _ => eps k) ?_).mpr
    · exact intervalIntegrable_const
    · rw [uIoo_of_le (he k hk)]
      exact hf k hk
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  calc
    (∫ x in e k..e (k + 1), f x) = ∫ _ in e k..e (k + 1), eps k :=
      intervalIntegral.integral_congr_Ioo_of_le (he k hk) (hf k hk)
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

theorem finite_step_integral_affine (e lam eps : ℕ → ℝ) (f0 fs : ℝ → ℝ) (n : ℕ) (s : ℝ)
    (he0 : ∀ k < n, e k ≤ e (k + 1))
    (hes : ∀ k < n, e k + s * lam k ≤ e (k + 1) + s * lam (k + 1))
    (hf0 : ∀ k < n, ∀ x ∈ Ioo (e k) (e (k + 1)), f0 x = eps k)
    (hfs : ∀ k < n, ∀ x ∈ Ioo (e k + s * lam k) (e (k + 1) + s * lam (k + 1)),
      fs x = eps k) :
    (∫ x in (e 0 + s * lam 0)..(e n + s * lam n), fs x) -
      (∫ x in e 0..e n, f0 x) =
        s * ∑ k ∈ Finset.range n, eps k * (lam (k + 1) - lam k) := by
  rw [finite_step_integral (fun k => e k + s * lam k) eps fs n hes hfs,
    finite_step_integral e eps f0 n he0 hf0, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem finite_step_jump_sum (eps lam : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), eps k * (lam (k + 1) - lam k)) =
      eps n * lam (n + 1) - eps 0 * lam 0 +
        ∑ k ∈ Finset.range n, (eps k - eps (k + 1)) * lam (k + 1) := by
  induction n with
  | zero => simp only [Finset.sum_range_one, Finset.sum_range_zero, zero_add, add_zero]; ring
  | succ n ih =>
    calc
      _ = (∑ k ∈ Finset.range (n + 1), eps k * (lam (k + 1) - lam k)) +
          eps (n + 1) * (lam (n + 1 + 1) - lam (n + 1)) := by
        rw [Finset.sum_range_succ]
      _ = _ := by rw [ih, Finset.sum_range_succ]; ring

theorem finite_step_jump_sum_fixed_boundary (eps lam : ℕ → ℝ) (n : ℕ)
    (h0 : lam 0 = 0) (hn : lam (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 1), eps k * (lam (k + 1) - lam k)) =
      ∑ k ∈ Finset.range n, (eps k - eps (k + 1)) * lam (k + 1) := by
  rw [finite_step_jump_sum, h0, hn]
  ring

end PiIrrationality
