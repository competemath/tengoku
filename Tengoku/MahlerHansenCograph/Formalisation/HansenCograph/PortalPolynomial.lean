/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.CographPortalFlags

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Factorially normalized portal polynomials

This file packages a finite portal vector as the factorially normalized
Bernstein polynomial used in the full-flag argument.  The shuffle convolution
becomes ordinary multiplication.
-/

open scoped BigOperators

namespace HansenCograph

/-- The factorially normalized Bernstein polynomial attached to a portal
vector of degree `n`.-/
noncomputable def portalPolynomial (n : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) *
      x ^ k * (1 - x) ^ (n - k)

theorem portalPolynomial_continuous (n : ℕ) (a : ℕ → ℝ) :
    Continuous (portalPolynomial n a) := by
  unfold portalPolynomial
  fun_prop

@[simp] theorem portalPolynomial_zero (n : ℕ) (a : ℕ → ℝ) :
    portalPolynomial n a 0 = a 0 / (n.factorial : ℝ) := by
  classical
  unfold portalPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    simp [zero_pow hkpos.ne']
  · simp

@[simp] theorem portalPolynomial_one (n : ℕ) (a : ℕ → ℝ) :
    portalPolynomial n a 1 = a n / (n.factorial : ℝ) := by
  classical
  unfold portalPolynomial
  rw [Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hsubpos : 0 < n - k := Nat.sub_pos_of_lt (lt_of_le_of_ne hkle hkn)
    simp [zero_pow hsubpos.ne']
  · simp

theorem portalPolynomial_zero_lt_one_iff (n : ℕ) (a : ℕ → ℝ) :
    portalPolynomial n a 0 < portalPolynomial n a 1 ↔ a 0 < a n := by
  simp only [portalPolynomial_zero, portalPolynomial_one]
  exact div_lt_div_iff_of_pos_right (by positivity)

/-- Collapse a bounded three-fold sum supported on the diagonal `s = k + l`.
Keeping this reindexing separate makes the shared-apex degree bookkeeping in
the portal product law explicit.-/
private theorem sum_range_diag
    (n m : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ s ∈ Finset.range (n + m + 1),
      ∑ k ∈ Finset.range (n + 1),
      ∑ l ∈ Finset.range (m + 1),
        if k + l = s then F s k l else 0) =
      ∑ k ∈ Finset.range (n + 1),
      ∑ l ∈ Finset.range (m + 1), F (k + l) k l := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hl' : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have hmem : k + l ∈ Finset.range (n + m + 1) :=
    Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single (k + l)]
  · simp
  · intro s hs hsne
    simp [Ne.symm hsne]
  · intro hnot
    exact False.elim (hnot hmem)

/-- Expanding the normalized shuffle convolution and summing over its output
degree removes the rank constraint.-/
theorem portalPolynomial_convolution_expand
    (n m : ℕ) (a b : ℕ → ℝ) (x : ℝ) :
    portalPolynomial (n + m) (portalShuffleConvolution n m a b) x =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) *
          (b l / ((l.factorial : ℝ) * ((m - l).factorial : ℝ))) *
            x ^ (k + l) * (1 - x) ^ ((n - k) + (m - l)) := by
  classical
  unfold portalPolynomial
  calc
    (∑ s ∈ Finset.range (n + m + 1),
        portalShuffleConvolution n m a b s /
            ((s.factorial : ℝ) * ((n + m - s).factorial : ℝ)) *
          x ^ s * (1 - x) ^ (n + m - s)) =
        ∑ s ∈ Finset.range (n + m + 1),
          (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
            if k + l = s then
              (a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) *
                (b l / ((l.factorial : ℝ) * ((m - l).factorial : ℝ)))
            else 0) * x ^ s * (1 - x) ^ (n + m - s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [portalShuffleConvolution_factorial_normalized]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) *
          (b l / ((l.factorial : ℝ) * ((m - l).factorial : ℝ))) *
            x ^ (k + l) * (1 - x) ^ (n + m - (k + l)) := by
      calc
        _ = ∑ s ∈ Finset.range (n + m + 1),
            ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
              if k + l = s then
                (a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) *
                  (b l / ((l.factorial : ℝ) * ((m - l).factorial : ℝ))) *
                    x ^ s * (1 - x) ^ (n + m - s)
              else 0 := by
          apply Finset.sum_congr rfl
          intro s hs
          conv_lhs => rw [mul_assoc]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l hl
          by_cases h : k + l = s <;> simp [h, mul_assoc]
        _ = _ := sum_range_diag n m (fun s k l ↦
          (a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) *
            (b l / ((l.factorial : ℝ) * ((m - l).factorial : ℝ))) *
              x ^ s * (1 - x) ^ (n + m - s))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hl' : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
      have hsub : n + m - (k + l) = (n - k) + (m - l) := by omega
      rw [hsub]

/-- The normalized portal polynomial turns the exact shuffle convolution into
ordinary multiplication.-/
theorem portalPolynomial_convolution
    (n m : ℕ) (a b : ℕ → ℝ) (x : ℝ) :
    portalPolynomial (n + m) (portalShuffleConvolution n m a b) x =
      portalPolynomial n a x * portalPolynomial m b x := by
  rw [portalPolynomial_convolution_expand]
  unfold portalPolynomial
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hl' : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  rw [pow_add, pow_add]
  ring

end HansenCograph
