/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite portal-vector shuffle convolution

This is the finite algebraic layer of the cograph full-flag argument.  It
does not assert that a graph join has this convolution: that requires the
separate restricted-product face-poset bridge.
-/

open scoped BigOperators

namespace HansenCograph

/-- The nonnegative shuffle coefficient for portal ranks `k,l` contributing
to output rank `s`.  The `if` records the rank constraint `k + l = s`.-/
noncomputable def portalShuffleKernel (n m s k l : ℕ) : ℝ :=
  if k + l = s then
    (Nat.choose s k : ℝ) * (Nat.choose (n + m - s) (n - k) : ℝ)
  else 0

/-- The finite portal-vector convolution.  The degrees `n,m` bound the two
input vectors; values outside those ranges are intentionally irrelevant.-/
noncomputable def portalShuffleConvolution
    (n m : ℕ) (a b : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
    portalShuffleKernel n m s k l * a k * b l

theorem portalShuffleKernel_nonneg (n m s k l : ℕ) :
    0 ≤ portalShuffleKernel n m s k l := by
  unfold portalShuffleKernel
  split_ifs <;> positivity

/- The two shuffle factors become the product of factorial denominators after
normalizing an output rank by `s! (n+m-s)!`.  This is the local algebraic
identity behind the Bernstein-polynomial product law. -/
theorem portalShuffleKernel_factorial_normalized
    {n m s k l : ℕ} (hk : k ≤ n) (hl : l ≤ m) (hkl : k + l = s) :
    portalShuffleKernel n m s k l /
        ((s.factorial : ℝ) * ((n + m - s).factorial : ℝ)) =
      1 / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) *
        (1 / ((l.factorial : ℝ) * ((m - l).factorial : ℝ))) := by
  have hks : k ≤ s := by omega
  have hns : n - k ≤ n + m - s := by omega
  have hsl : s - k = l := by omega
  have hrest : n + m - s - (n - k) = m - l := by omega
  unfold portalShuffleKernel
  rw [ite_eq_left hkl, Nat.cast_choose ℝ hks, Nat.cast_choose ℝ hns]
  rw [hsl, hrest]
  have hsk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hslfac : (l.factorial : ℝ) ≠ 0 := by positivity
  have hnk : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  have hml : ((m - l).factorial : ℝ) ≠ 0 := by positivity
  have hs : (s.factorial : ℝ) ≠ 0 := by positivity
  have hnsfac : ((n + m - s).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/- The preceding identity can be summed rank-by-rank: dividing the output
coefficient by its factorial normalization turns the shuffle convolution into
the finite convolution of the two normalized input vectors. -/
theorem portalShuffleConvolution_factorial_normalized
    (n m s : ℕ) (a b : ℕ → ℝ) :
    portalShuffleConvolution n m a b s /
        ((s.factorial : ℝ) * ((n + m - s).factorial : ℝ)) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        if k + l = s then
          (a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) *
            (b l / ((l.factorial : ℝ) * ((m - l).factorial : ℝ)))
        else 0 := by
  unfold portalShuffleConvolution
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : k + l = s
  · have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hl' : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    have hnorm := portalShuffleKernel_factorial_normalized hk' hl' h
    simp only [ite_eq_left h]
    calc
      (portalShuffleKernel n m s k l * a k * b l) /
          ((s.factorial : ℝ) * ((n + m - s).factorial : ℝ)) =
          (portalShuffleKernel n m s k l /
            ((s.factorial : ℝ) * ((n + m - s).factorial : ℝ))) * a k * b l := by
              ring
      _ = (1 / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) *
            (1 / ((l.factorial : ℝ) * ((m - l).factorial : ℝ)))) * a k * b l := by
              rw [hnorm]
        _ = (a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) *
            (b l / ((l.factorial : ℝ) * ((m - l).factorial : ℝ))) := by
              field_simp
  · simp [portalShuffleKernel, h]

/-- A portal convolution is nonnegative when both bounded input vectors are.-/
theorem portalShuffleConvolution_nonneg
    {n m : ℕ} {a b : ℕ → ℝ}
    (ha : ∀ k < n + 1, 0 ≤ a k)
    (hb : ∀ l < m + 1, 0 ≤ b l)
    (s : ℕ) :
    0 ≤ portalShuffleConvolution n m a b s := by
  unfold portalShuffleConvolution
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro l hl
  exact mul_nonneg
    (mul_nonneg (portalShuffleKernel_nonneg n m s k l)
      (ha k (Finset.mem_range.mp hk)))
    (hb l (Finset.mem_range.mp hl))

/-- Explicit lower-bound transfer for the portal convolution.  This is purely
finite algebra: the hypotheses provide componentwise lower bounds and the
nonnegativity needed to multiply those inequalities.-/
theorem portalShuffleConvolution_le
    {n m : ℕ} {a a' b b' : ℕ → ℝ}
    (ha0 : ∀ k < n + 1, 0 ≤ a k)
    (hb0 : ∀ l < m + 1, 0 ≤ b l)
    (haa' : ∀ k < n + 1, a k ≤ a' k)
    (hbb' : ∀ l < m + 1, b l ≤ b' l)
    (s : ℕ) :
    portalShuffleConvolution n m a b s ≤
      portalShuffleConvolution n m a' b' s := by
  unfold portalShuffleConvolution
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro l hl
  have hk' : k < n + 1 := Finset.mem_range.mp hk
  have hl' : l < m + 1 := Finset.mem_range.mp hl
  have hab : a k * b l ≤ a' k * b' l := by
    calc
      a k * b l ≤ a' k * b l := mul_le_mul_of_nonneg_right (haa' k hk') (hb0 l hl')
      _ ≤ a' k * b' l := mul_le_mul_of_nonneg_left (hbb' l hl')
        (le_trans (ha0 k hk') (haa' k hk'))
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left hab (portalShuffleKernel_nonneg n m s k l))

/-- A strict increase in one bounded portal coordinate transfers to a strict
increase of the convolution at `s` when its shuffle coefficient and the
opposite-factor coordinate are positive.  This is finite algebra only.-/
theorem portalShuffleConvolution_strict_of_witness
    {n m : ℕ} {a a' b : ℕ → ℝ} {s k₀ l₀ : ℕ}
    (ha0 : ∀ k < n + 1, 0 ≤ a k)
    (hb0 : ∀ l < m + 1, 0 ≤ b l)
    (haa' : ∀ k < n + 1, a k ≤ a' k)
    (hk₀ : k₀ < n + 1) (hl₀ : l₀ < m + 1)
    (hkernel : 0 < portalShuffleKernel n m s k₀ l₀)
    (hstrict : a k₀ < a' k₀)
    (hother : 0 < b l₀) :
    portalShuffleConvolution n m a b s <
      portalShuffleConvolution n m a' b s := by
  have hbase_nonneg : 0 ≤ portalShuffleConvolution n m a b s :=
    portalShuffleConvolution_nonneg ha0 hb0 s
  let t : ℕ → ℕ → ℝ := fun k l =>
    portalShuffleKernel n m s k l * (a' k - a k) * b l
  have ht_nonneg (k l : ℕ)
      (hk : k < n + 1) (hl : l < m + 1) : 0 ≤ t k l := by
    dsimp [t]
    exact mul_nonneg
      (mul_nonneg (portalShuffleKernel_nonneg n m s k l)
        (sub_nonneg.mpr (haa' k hk)))
      (hb0 l hl)
  have ht_strict : 0 < t k₀ l₀ := by
    dsimp [t]
    exact mul_pos (mul_pos hkernel (sub_pos.mpr hstrict)) hother
  have hsum_nonneg :
      0 ≤ ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1), t k l := by
    apply Finset.sum_nonneg
    intro k hk
    apply Finset.sum_nonneg
    intro l hl
    exact ht_nonneg k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)
  have hsingle :
      t k₀ l₀ ≤ ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1), t k l := by
    calc
      t k₀ l₀ ≤ ∑ l ∈ Finset.range (m + 1), t k₀ l := by
        exact Finset.single_le_sum
          (fun l hl => ht_nonneg k₀ l hk₀ (Finset.mem_range.mp hl))
          (Finset.mem_range.mpr hl₀)
      _ ≤ ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1), t k l := by
        exact Finset.single_le_sum
          (fun k hk => Finset.sum_nonneg (fun l hl =>
            ht_nonneg k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)))
          (Finset.mem_range.mpr hk₀)
  have hsum_pos :
      0 < ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1), t k l :=
    lt_of_lt_of_le ht_strict hsingle
  have hdiff :
      portalShuffleConvolution n m a' b s -
          portalShuffleConvolution n m a b s =
        ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1), t k l := by
    unfold portalShuffleConvolution
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    dsimp [t]
    ring
  rw [← hdiff] at hsum_pos
  linarith

/-- The second-vector orientation of the finite strictness witness.-/
theorem portalShuffleConvolution_strict_of_witness_right
    {n m : ℕ} {a b b' : ℕ → ℝ} {s k₀ l₀ : ℕ}
    (ha0 : ∀ k < n + 1, 0 ≤ a k)
    (hb0 : ∀ l < m + 1, 0 ≤ b l)
    (hbb' : ∀ l < m + 1, b l ≤ b' l)
    (hk₀ : k₀ < n + 1) (hl₀ : l₀ < m + 1)
    (hkernel : 0 < portalShuffleKernel n m s k₀ l₀)
    (hother : 0 < a k₀)
    (hstrict : b l₀ < b' l₀) :
    portalShuffleConvolution n m a b s <
      portalShuffleConvolution n m a b' s := by
  have hbase_nonneg : 0 ≤ portalShuffleConvolution n m a b s :=
    portalShuffleConvolution_nonneg ha0 hb0 s
  let t : ℕ → ℕ → ℝ := fun k l =>
    portalShuffleKernel n m s k l * a k * (b' l - b l)
  have ht_nonneg (k l : ℕ)
      (hk : k < n + 1) (hl : l < m + 1) : 0 ≤ t k l := by
    dsimp [t]
    exact mul_nonneg
      (mul_nonneg (portalShuffleKernel_nonneg n m s k l) (ha0 k hk))
      (sub_nonneg.mpr (hbb' l hl))
  have ht_strict : 0 < t k₀ l₀ := by
    dsimp [t]
    exact mul_pos (mul_pos hkernel hother) (sub_pos.mpr hstrict)
  have hsingle :
      t k₀ l₀ ≤ ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1), t k l := by
    calc
      t k₀ l₀ ≤ ∑ l ∈ Finset.range (m + 1), t k₀ l := by
        exact Finset.single_le_sum
          (fun l hl => ht_nonneg k₀ l hk₀ (Finset.mem_range.mp hl))
          (Finset.mem_range.mpr hl₀)
      _ ≤ ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1), t k l := by
        exact Finset.single_le_sum
          (fun k hk => Finset.sum_nonneg (fun l hl =>
            ht_nonneg k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)))
          (Finset.mem_range.mpr hk₀)
  have hsum_pos :
      0 < ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1), t k l :=
    lt_of_lt_of_le ht_strict hsingle
  have hdiff :
      portalShuffleConvolution n m a b' s -
          portalShuffleConvolution n m a b s =
        ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1), t k l := by
    unfold portalShuffleConvolution
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    dsimp [t]
    ring
  rw [← hdiff] at hsum_pos
  linarith

/-- A two-sided finite strictness interface.  Either an explicitly positive
left witness or an explicitly positive right witness forces strict growth
after both portal vectors are enlarged.-/
theorem portalShuffleConvolution_strict_of_witness_either
    {n m : ℕ} {a a' b b' : ℕ → ℝ} (s : ℕ)
    (ha0 : ∀ k < n + 1, 0 ≤ a k)
    (hb0 : ∀ l < m + 1, 0 ≤ b l)
    (haa' : ∀ k < n + 1, a k ≤ a' k)
    (hbb' : ∀ l < m + 1, b l ≤ b' l)
    (hwitness :
      (∃ k l, k < n + 1 ∧ l < m + 1 ∧
        0 < portalShuffleKernel n m s k l ∧ a k < a' k ∧ 0 < b l) ∨
      (∃ k l, k < n + 1 ∧ l < m + 1 ∧
        0 < portalShuffleKernel n m s k l ∧ 0 < a k ∧ b l < b' l)) :
    portalShuffleConvolution n m a b s <
      portalShuffleConvolution n m a' b' s := by
  rcases hwitness with hleft | hright
  · rcases hleft with ⟨k, l, hk, hl, hkernel, hstrict, hother⟩
    have hfirst := portalShuffleConvolution_strict_of_witness
      ha0 hb0 haa' hk hl hkernel hstrict hother
    have ha'0 : ∀ i < n + 1, 0 ≤ a' i := fun i hi =>
      le_trans (ha0 i hi) (haa' i hi)
    have hsecond :
        portalShuffleConvolution n m a' b s ≤
          portalShuffleConvolution n m a' b' s :=
      portalShuffleConvolution_le ha'0 hb0 (fun i hi => le_rfl) hbb' s
    exact hfirst.trans_le hsecond
  · rcases hright with ⟨k, l, hk, hl, hkernel, hother, hstrict⟩
    have hfirst := portalShuffleConvolution_strict_of_witness_right
      ha0 hb0 hbb' hk hl hkernel hother hstrict
    have hb'0 : ∀ i < m + 1, 0 ≤ b' i := fun i hi =>
      le_trans (hb0 i hi) (hbb' i hi)
    have hsecond :
        portalShuffleConvolution n m a b' s ≤
          portalShuffleConvolution n m a' b' s :=
      portalShuffleConvolution_le ha0 hb'0 haa' (fun i hi => le_rfl) s
    exact hfirst.trans_le hsecond

end HansenCograph
