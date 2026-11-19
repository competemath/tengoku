import Tengoku.Seed.LinearAlgebra.Lagrange
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators

/-!
# LN97 Lemma 6.55: a bound on power sums bounds each root

We use polynomial interpolation instead of logarithmic power series.
A Lagrange polynomial isolates each distinct value in the family, including
its (positive) multiplicity. Its weighted power sums are finite linear
combinations of shifts of the original power sums. Exponential growth then
rules out any value whose norm exceeds the proposed bound.
-/

private theorem le_of_powers_bounded {a B K : ℝ} (hB : 0 < B)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ K * B ^ n) : a ≤ B := by
  by_contra! hab
  have hratio : 1 < a / B := (lt_div_iff₀ hB).mpr (by simpa using hab)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max K 1) hratio
  have hn0 : 0 < n := by
    by_contra! hn0
    have : n = 0 := Nat.eq_zero_of_le_zero hn0
    simp only [this, pow_zero] at hn
    exact (not_lt_of_ge (le_max_right K 1)) hn
  have hb := (div_le_iff₀ (pow_pos hB n)).mpr (h n hn0)
  rw [← div_pow] at hb
  exact (not_lt_of_ge (hb.trans (le_max_left K 1))) hn

/-- **LN97 Lemma 6.55.** A uniform exponential bound on all positive
power sums bounds the norm of every member of the finite family.
Repeated values are allowed.
@isnad1 id=le.2h5v.s6.9361cac1a098 from=translated src=- shape=dcd35aaa vocab=55c9deef
-/
theorem ln97_6_55 {ι : Type*} [Fintype ι] (omega : ι → ℂ)
    {B C : ℝ} (hB : 0 < B)
    (hbound : ∀ s : ℕ, 0 < s → ‖∑ i, omega i ^ s‖ ≤ C * B ^ s)
    (j : ι) : ‖omega j‖ ≤ B := by
  classical
  let values : Finset ℂ := Finset.univ.image omega
  let p : Polynomial ℂ := Lagrange.basis values id (omega j)
  let fiber : Finset ι := Finset.univ.filter (fun i => omega i = omega j)
  have hfiber : 1 ≤ (fiber.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr
      (show fiber.Nonempty from ⟨j, by simp [fiber]⟩))
  have heval (i : ι) : p.eval (omega i) = if omega i = omega j then 1 else 0 := by
    have hi : omega i ∈ values := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    split_ifs with hij
    · rw [hij]
      exact Lagrange.eval_basis_self (fun _ _ _ _ h => h)
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    · exact Lagrange.eval_basis_of_ne (v := id) (Ne.symm hij) hi
  have hisolate (s : ℕ) :
      ∑ i, omega i ^ s * p.eval (omega i) = (fiber.card : ℂ) * omega j ^ s := by
    simp_rw [heval]
    calc
      ∑ i, omega i ^ s * (if omega i = omega j then 1 else 0) =
          ∑ i ∈ fiber, omega j ^ s := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hij <;> simp [hij]
      _ = _ := by simp
  have hshift (s : ℕ) :
      ∑ i, omega i ^ s * p.eval (omega i) =
        ∑ k ∈ p.support, p.coeff k * ∑ i, omega i ^ (s + k) := by
    simp_rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
    ring
  let K : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * C * B ^ k
  apply le_of_powers_bounded hB (K := K)
  intro s hs
  calc
    ‖omega j‖ ^ s ≤ (fiber.card : ℝ) * ‖omega j‖ ^ s := by
      nlinarith [pow_nonneg (norm_nonneg (omega j)) s]
    _ = ‖∑ i, omega i ^ s * p.eval (omega i)‖ := by
      rw [hisolate, norm_mul, norm_pow, Complex.norm_natCast]
    _ = ‖∑ k ∈ p.support, p.coeff k * ∑ i, omega i ^ (s + k)‖ := by rw [hshift]
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k * ∑ i, omega i ^ (s + k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (C * B ^ (s + k)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound (s + k) (by omega)) (norm_nonneg _)
    _ = K * B ^ s := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_add]
      ring

/-- It suffices to control positive powers along any fixed arithmetic
subsequence. This is the form used after passing to a sufficiently large
finite extension in LN97 Theorem 6.56.
@isnad1 id=le.3h6v.s7.927fe125e0b7 from=translated src=- shape=dcf57954 vocab=55c9deef
-/
theorem ln97_6_55_of_multiples {ι : Type*} [Fintype ι] (omega : ι → ℂ)
    {B C : ℝ} (hB : 0 < B) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ s : ℕ, 0 < s →
      ‖∑ i, omega i ^ (r * s)‖ ≤ C * B ^ (r * s))
    (j : ι) : ‖omega j‖ ≤ B := by
  have h := ln97_6_55 (fun i => omega i ^ r) (pow_pos hB r)
    (C := C) (by simpa only [← pow_mul] using hbound) j
  rw [norm_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB.le (Nat.ne_of_gt hr)).mp h

/-- Once an extension-field character sum has a finite power-sum
representation, a uniform coarse bound on its extensions gives the sharp
bound for its first sum. The representation and extension estimates remain
explicit hypotheses; this lemma does not assert they have been constructed.
@isnad1 id=le.3h5v.s7.9e10cdfa9b1e from=translated src=- shape=863897ba vocab=fe5ca5eb
-/
theorem norm_sum_le_of_powerSum_bound {ι : Type*} [Fintype ι]
    (omega : ι → ℂ) {B C : ℝ} (hB : 0 < B) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ s : ℕ, 0 < s →
      ‖∑ i, omega i ^ (r * s)‖ ≤ C * B ^ (r * s)) :
    ‖∑ i, omega i‖ ≤ (Fintype.card ι : ℝ) * B := by
  calc
    ‖∑ i, omega i‖ ≤ ∑ i, ‖omega i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ =>
      ln97_6_55_of_multiples omega hB hr hbound i
    _ = _ := by simp

end MagicSquares.LN97
