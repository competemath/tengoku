import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.RatTails

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #265 — Part U9: regularised tail estimate

If `a_m ≥ e^m` for `m ≥ N`, then for `n ≥ N`, splitting the tail at
`M = ⌈log a_n⌉`: the first `M` terms are each `≤ 1/a_n`; for `j ≥ M`,
`1/a_{n+j} ≤ e^{-(n+j)} ≤ e^{-j}/a_n`… precisely `∑_{j≥M} e^{-(n+j)} ≤ e^{-M}/(1-e^{-1})
≤ (1/a_n)·1.59`.  Hence `T n ≤ (⌈log a_n⌉ + 2)/a_n = regF a n / a_n`.
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

/-- `1/(1 - e^{-1}) ≤ 2`.
@isnad1 id=le.0h0v.s5.dd53103cef85 from=translated src=- shape=843d0ec6 vocab=1e76ec75
-/
theorem inv_one_sub_exp_neg_one_le_two : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hrhalf : Real.exp (-1) ≤ 1 / 2 := by
    calc Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
      _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he
      _ = 1 / 2 := by norm_num
  have h12 : (1 / 2 : ℝ) ≤ 1 - Real.exp (-1) := by linarith
  calc (1 - Real.exp (-1))⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h12
    _ = 2 := by norm_num

/--
@isnad1 id=lt.0h0v.s4.7d73c39a3ee4 from=translated src=- shape=00b7d787 vocab=379b737d
-/
theorem exp_neg_one_lt_one : Real.exp (-1) < 1 := by
  rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)

/-- `e^{-⌈log x⌉} ≤ 1/x` for `x > 0`.
@isnad1 id=le.1h1v.s5.af61628179bf from=translated src=- shape=cd90b82f vocab=557b3076
-/
theorem exp_neg_ceil_log_le {x : ℝ} (hx : 0 < x) :
    Real.exp (-((⌈Real.log x⌉₊ : ℕ) : ℝ)) ≤ 1 / x := by
  have hl : Real.log x ≤ ((⌈Real.log x⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  rw [Real.exp_neg, one_div]
  apply inv_anti₀ hx
  calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
    _ ≤ _ := Real.exp_le_exp.mpr hl

/-- Pointwise bound on the far tail.
@isnad1 id=le.2h5v.s6.d480bd281c77 from=translated src=- shape=64d3ac59 vocab=953ef376
-/
theorem far_term_le {N n M k : ℕ} (hn : N ≤ n)
    (hN : ∀ m ≥ N, Real.exp (m : ℝ) ≤ (a m : ℝ)) :
    recip a (k + M + n) ≤ Real.exp (-(M : ℝ)) * Real.exp (-1) ^ k := by
  have hge := hN (k + M + n) (by omega)
  have hpos : 0 < Real.exp ((k + M + n : ℕ) : ℝ) := Real.exp_pos _
  unfold recip
  calc 1 / (a (k + M + n) : ℝ) ≤ 1 / Real.exp ((k + M + n : ℕ) : ℝ) :=
        one_div_le_one_div_of_le hpos hge
    _ ≤ 1 / Real.exp ((k : ℝ) + M) := by
        apply one_div_le_one_div_of_le (Real.exp_pos _)
        apply Real.exp_le_exp.mpr
        push_cast
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
    _ = Real.exp (-(M : ℝ)) * Real.exp (-1) ^ k := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, one_div, ← Real.exp_neg]
        congr 1
        ring

/-- Far tail sum bound.
@isnad1 id=le.3h4v.s6.19a0c5e57d97 from=translated src=- shape=b405a913 vocab=f951fd3f
-/
theorem far_tail_le (ha : IsRationalPair a) {N n M : ℕ} (hn : N ≤ n)
    (hN : ∀ m ≥ N, Real.exp (m : ℝ) ≤ (a m : ℝ)) :
    ∑' k, recip a (k + M + n) ≤ 2 * Real.exp (-(M : ℝ)) := by
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hgs : Summable (fun k : ℕ => Real.exp (-(M : ℝ)) * Real.exp (-1) ^ k) :=
    (summable_geometric_of_lt_one hr0 exp_neg_one_lt_one).mul_left _
  have hs : Summable (fun k => recip a (k + n)) :=
    (summable_nat_add_iff n).mpr (summable_recip ha)
  have hs2 : Summable (fun k => recip a (k + M + n)) :=
    (summable_nat_add_iff M).mpr hs
  have h2 : ∑' k, recip a (k + M + n) ≤
      Real.exp (-(M : ℝ)) * (1 - Real.exp (-1))⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 exp_neg_one_lt_one, ← tsum_mul_left]
    exact hs2.tsum_le_tsum (fun k => far_term_le hn hN) hgs
  calc _ ≤ Real.exp (-(M : ℝ)) * (1 - Real.exp (-1))⁻¹ := h2
    _ ≤ Real.exp (-(M : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left inv_one_sub_exp_neg_one_le_two (Real.exp_pos _).le
    _ = 2 * Real.exp (-(M : ℝ)) := by ring

/-- Near part bound.
@isnad1 id=le.1h3v.s6.5d67501a310f from=translated src=- shape=25b07ffb vocab=6b5a2904
-/
theorem near_sum_le (ha : IsRationalPair a) (n M : ℕ) :
    ∑ k ∈ Finset.range M, recip a (k + n) ≤ M * (1 / (a n : ℝ)) := by
  have hxpos : 0 < (a n : ℝ) := by
    have : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
    linarith
  have hle : ∀ k ∈ Finset.range M, recip a (k + n) ≤ 1 / (a n : ℝ) := by
    intro k _
    unfold recip
    have : (a n : ℝ) ≤ a (k + n) := by exact_mod_cast ha.1.monotone (by omega)
    exact one_div_le_one_div_of_le hxpos this
  calc _ ≤ ∑ k ∈ Finset.range M, (1 / (a n : ℝ)) := Finset.sum_le_sum hle
    _ = M * (1 / (a n : ℝ)) := by simp

/--
@isnad1 id=eq.1h3v.s6.4847b4a1bc50 from=translated src=- shape=3a302345 vocab=88d9885e
-/
theorem T_split (ha : IsRationalPair a) (n M : ℕ) :
    T a n = ∑ k ∈ Finset.range M, recip a (k + n) + ∑' k, recip a (k + M + n) := by
  have hs : Summable (fun k => recip a (k + n)) :=
    (summable_nat_add_iff n).mpr (summable_recip ha)
  unfold T tail
  rw [← hs.sum_add_tsum_nat_add M]

/--
@isnad1 id=eventual.2h1v.s5.13756d90b5d1 from=translated src=- shape=bace056d vocab=d1b9ff0b
-/
theorem tail_regular (ha : IsRationalPair a)
    (hexp : ∀ᶠ m : ℕ in atTop, Real.exp (m : ℝ) ≤ (a m : ℝ)) :
    ∀ᶠ n in atTop, T a n ≤ regF a n / (a n : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hexp
  filter_upwards [eventually_ge_atTop N] with n hn
  have hxpos : 0 < (a n : ℝ) := by
    have : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
    linarith
  have h1 := near_sum_le ha n ⌈Real.log (a n : ℝ)⌉₊
  have h2 := far_tail_le ha (M := ⌈Real.log (a n : ℝ)⌉₊) hn hN
  have h3 := exp_neg_ceil_log_le hxpos
  rw [T_split ha n ⌈Real.log (a n : ℝ)⌉₊]
  unfold regF
  calc _ ≤ (⌈Real.log (a n : ℝ)⌉₊ : ℝ) * (1 / (a n : ℝ)) + 2 * (1 / (a n : ℝ)) := by
        linarith
    _ = ((⌈Real.log (a n : ℝ)⌉₊ : ℝ) + 2) / (a n : ℝ) := by ring

end Erdos265
