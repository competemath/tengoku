/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.EllipticEAGM
import Tengoku.Seed.Analysis.Real.Pi.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.8.2: Salamin's formula for `π`

The Brent–Salamin (Gauss–Legendre) algorithm rests on Salamin's formula: with the AGM
iteration `(a_j, b_j)` started at `(1, 1/√2)` and `c_j² = a_j² − b_j²`,

  `π = 4 AGM(1, 1/√2)² / (1 − ∑_{j≥1} 2^(j+1) c_j²)`                      (`salamin_formula`).

Proof: at `k = k' = 1/√2`, Gauss's formula for `E` (`ellipticE_eq_AGM_sum`) gives
`E = (1 − S) K` with `S = ∑_{j≥0} 2^(j−1) c_j² = 1/4 + T/4`, `T = ∑_{j≥1} 2^(j+1) c_j²`
(`c_0² = 1/2`); the Legendre relation `2EK − K² = π/2` (`legendre_relation_sqrt_half`) becomes
`K² (1 − T)/2 = π/2`; and Gauss's theorem `K = π/(2 AGM)` (`ellipticK_salaminB0`) turns this
into `π (1 − T) = 4 AGM²` (`salamin_identity`), whence the denominator is positive
(`salamin_denominator_pos`) and the formula follows.

Also here: `agmCsq a b j = a_j² − b_j²` with the cancellation-free form
`c_{j+1} = (a_j − b_j)/2` (`agmCsq_succ`), the starting value `salaminB0 = 1/√2` and its facts,
and `summable_salaminSum`.

**The iterate and its error bound.**  With `s_N = 1/2 − ∑_{j=1}^{N} 2^j c_j²` (`salaminS`,
recurrence `s_{N+1} = s_N − 2^(N+1)((a_N − b_N)/2)²`, `salaminS_succ`) the Brent–Salamin
iterate is `π_N = 2 a_{N+1}²/s_N` (`salaminApprox`).  Writing `s_N = s_∞ + r_N` with
`s_∞ = (1 − T)/2 = 2 AGM²/π > 1/3` (`salaminS_eq`, `salaminS_limit_gt`,
`pi_eq_div_salaminS_limit`) and the tail `r_N = ∑_{j≥N} 2^(j+1) c_{j+1}²` (`salaminTail`), the
quarter-decay of the gap gives `r_N ≤ (4/7) 2^N (a_N − b_N)²` (`salaminTail_le`), and
`a_{N+1}² − AGM² ≤ (3/8)(a_N − b_N)²` from the quadratic gap bound; hence for `N ≥ 1`

  `−(48/7) 2^N (a_N − b_N)² ≤ π_N − π ≤ (9/4)(a_N − b_N)²`
  (`le_salaminApprox_sub_pi`, `salaminApprox_sub_pi_le`),

so `|π_N − π| ≤ 7 · 2^N (a_N − b_N)²` (`abs_salaminApprox_sub_pi_le`): the error is bounded by
a quantity the algorithm computes anyway, which makes a floating-point implementation
self-validating; `π_N → π` (`tendsto_salaminApprox`).

Not formalized (next): the floating-point enclosure of the iteration and the correctly rounded
`π` (`AzFloat`).
-/

namespace Azurite

namespace BZ

open Real Filter Topology

/-! ### `c_j²` along the AGM -/

/-- `c_j² = a_j² − b_j²`.-/
noncomputable def agmCsq (a b : ℝ) (j : ℕ) : ℝ := agmA a b j ^ 2 - agmB a b j ^ 2

variable {a b : ℝ}

/-- The cancellation-free form `c_{j+1} = (a_j − b_j)/2`.-/
theorem agmCsq_succ (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    agmCsq a b (j + 1) = ((agmA a b j - agmB a b j) / 2) ^ 2 := by
  obtain ⟨hA, hB⟩ := agm_pos ha hb j
  rw [agmCsq, agmA_succ, agmB_succ, Real.sq_sqrt (by positivity)]
  ring

/-! ### The starting value `1/√2` -/

/-- The Brent–Salamin starting value `b₀ = 1/√2 = k = k'`.-/
noncomputable def salaminB0 : ℝ := 1 / Real.sqrt 2

theorem salaminB0_pos : 0 < salaminB0 := by unfold salaminB0; positivity

theorem salaminB0_lt_one : salaminB0 < 1 := by
  unfold salaminB0
  rw [div_lt_one (by positivity), Real.lt_sqrt zero_le_one]
  norm_num

theorem salaminB0_sq : salaminB0 ^ 2 = 1 / 2 := by
  unfold salaminB0
  rw [div_pow, one_pow, Real.sq_sqrt zero_le_two]

/-- `1/√2` is its own complementary modulus.-/
theorem sqrt_one_sub_salaminB0_sq : Real.sqrt (1 - salaminB0 ^ 2) = salaminB0 := by
  rw [salaminB0_sq, show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.sqrt_inv, salaminB0, one_div]

/-- Gauss's theorem at `1/√2`: `K(1/√2) = π/(2 AGM(1, 1/√2))`.-/
theorem ellipticK_salaminB0 : ellipticK salaminB0 = π / (2 * AGM 1 salaminB0) := by
  have h := one_div_AGM_one salaminB0_pos salaminB0_lt_one.le
  rw [sqrt_one_sub_salaminB0_sq] at h
  have hM : 0 < AGM 1 salaminB0 := AGM_one_pos salaminB0_pos
  field_simp at h ⊢
  linarith

/-! ### Salamin's formula -/

/-- `T = ∑_{j≥1} 2^(j+1) c_j²` for the AGM started at `(1, 1/√2)` (indexed from `0`).-/
noncomputable def salaminSum : ℝ := ∑' j : ℕ, 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1)

theorem summable_salaminSum :
    Summable fun j : ℕ => 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1) := by
  have h := summable_agm_c_sq one_pos salaminB0_pos salaminB0_lt_one.le
  have h2 := (summable_nat_add_iff (f := fun j : ℕ =>
    2 ^ j / 2 * (agmA 1 salaminB0 j ^ 2 - agmB 1 salaminB0 j ^ 2)) 1).mpr h
  refine (h2.mul_left 4).congr fun j => ?_
  simp only [agmCsq]
  ring

/-! ### The Brent–Salamin iterate -/

local notation "sA" => agmA 1 salaminB0
local notation "sB" => agmB 1 salaminB0

theorem salamin_agm_pos (n : ℕ) : 0 < sA n ∧ 0 < sB n := agm_pos one_pos salaminB0_pos n

theorem salaminB0_gt : 2 / 3 < salaminB0 := by
  unfold salaminB0
  rw [lt_div_iff₀ (by positivity)]
  have : Real.sqrt 2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

theorem salamin_agmA_one : sA 1 = (1 + salaminB0) / 2 := by rw [agmA_succ, agmA_zero, agmB_zero]

theorem salamin_agmB_one : sB 1 = Real.sqrt salaminB0 := by
  rw [agmB_succ, agmA_zero, agmB_zero, one_mul]

theorem salamin_agmB_one_sq : sB 1 ^ 2 = salaminB0 := by
  rw [salamin_agmB_one, Real.sq_sqrt salaminB0_pos.le]

theorem salamin_agmB_one_gt : 2 / 3 < sB 1 := by
  rw [salamin_agmB_one]
  have h0 := salaminB0_pos
  have h1 := salaminB0_lt_one
  calc 2 / 3 < salaminB0 := salaminB0_gt
    _ ≤ Real.sqrt salaminB0 := (Real.le_sqrt' h0).mpr (by nlinarith)

/-- `a_n ≤ 1` for `n ≥ 1`.-/
theorem salamin_agmA_le_one {n : ℕ} (hn : 1 ≤ n) : sA n ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  calc sA (m + 1) ≤ sA 1 := by simpa using agmA_antitone one_pos salaminB0_pos (Nat.zero_le m)
    _ = (1 + salaminB0) / 2 := salamin_agmA_one
    _ ≤ 1 := by linarith [salaminB0_lt_one]

/-- `b_n > 2/3` for `n ≥ 1`.-/
theorem salamin_agmB_gt {n : ℕ} (hn : 1 ≤ n) : 2 / 3 < sB n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  calc 2 / 3 < sB 1 := salamin_agmB_one_gt
    _ ≤ sB (m + 1) := by simpa using agmB_monotone one_pos salaminB0_pos (Nat.zero_le m)

/-- The gap is in the quarter-decay regime from the start: `a_n − b_n ≤ 2 b_1` for `n ≥ 1`.-/
theorem salamin_gap_le_two_mul {n : ℕ} (hn : 1 ≤ n) : sA n - sB n ≤ 2 * sB 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := agm_gap_le_half_pow one_pos salaminB0_pos m
  have hA1 := salamin_agmA_le_one le_rfl
  have hB1 := salamin_agmB_one_gt
  have h2 : (sA 1 - sB 1) / 2 ^ m ≤ sA 1 - sB 1 :=
    div_le_self (sub_nonneg.mpr (agmB_le_agmA one_pos salaminB0_pos le_rfl))
      (one_le_pow₀ (by norm_num))
  linarith

/-- `s_N = 1/2 − ∑_{j=1}^{N} 2^j c_j²`.-/
noncomputable def salaminS (N : ℕ) : ℝ :=
  1 / 2 - ∑ j ∈ Finset.range N, 2 ^ (j + 1) * agmCsq 1 salaminB0 (j + 1)

theorem salaminS_zero : salaminS 0 = 1 / 2 := by simp [salaminS]

/-- The recurrence the algorithm runs: `s_{N+1} = s_N − 2^(N+1) ((a_N − b_N)/2)²`.-/
theorem salaminS_succ (N : ℕ) :
    salaminS (N + 1) = salaminS N - 2 ^ (N + 1) * ((sA N - sB N) / 2) ^ 2 := by
  rw [salaminS, salaminS, Finset.sum_range_succ, agmCsq_succ one_pos salaminB0_pos]
  ring

/-- The Brent–Salamin iterate `π_N = 2 a_{N+1}²/s_N`.-/
noncomputable def salaminApprox (N : ℕ) : ℝ := 2 * sA (N + 1) ^ 2 / salaminS N

/-- The tail `r_N = ∑_{j≥N} 2^(j+1) c_{j+1}²`, so that `s_N = s_∞ + r_N`.-/
noncomputable def salaminTail (N : ℕ) : ℝ :=
  ∑' i : ℕ, 2 ^ (i + N + 1) * agmCsq 1 salaminB0 (i + N + 1)

theorem summable_salaminSum_add (N : ℕ) :
    Summable fun i : ℕ => 2 ^ (i + N + 2) * agmCsq 1 salaminB0 (i + N + 1) :=
  (summable_nat_add_iff (f := fun j : ℕ => 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1)) N).mpr
    summable_salaminSum

theorem summable_salaminTail (N : ℕ) :
    Summable fun i : ℕ => 2 ^ (i + N + 1) * agmCsq 1 salaminB0 (i + N + 1) := by
  refine ((summable_salaminSum_add N).div_const 2).congr fun i => ?_
  ring

theorem agmCsq_succ_nonneg (ha : 0 < a) (hb : 0 < b) (j : ℕ) : 0 ≤ agmCsq a b (j + 1) := by
  rw [agmCsq_succ ha hb]; positivity

theorem salaminTail_nonneg (N : ℕ) : 0 ≤ salaminTail N :=
  tsum_nonneg fun i => mul_nonneg (by positivity) (agmCsq_succ_nonneg one_pos salaminB0_pos _)

/-- `s_N = (1 − T)/2 + r_N`.-/
theorem salaminS_eq (N : ℕ) : salaminS N = (1 - salaminSum) / 2 + salaminTail N := by
  have h : (∑ i ∈ Finset.range N, 2 ^ (i + 2) * agmCsq 1 salaminB0 (i + 1))
      + ∑' i : ℕ, 2 ^ (i + N + 2) * agmCsq 1 salaminB0 (i + N + 1) = salaminSum :=
    Summable.sum_add_tsum_nat_add' (f := fun j : ℕ => 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1))
      (k := N) (summable_salaminSum_add N)
  have e1 : ∑ j ∈ Finset.range N, 2 ^ (j + 1) * agmCsq 1 salaminB0 (j + 1)
      = (∑ j ∈ Finset.range N, 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1)) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : salaminTail N
      = (∑' i : ℕ, 2 ^ (i + N + 2) * agmCsq 1 salaminB0 (i + N + 1)) / 2 := by
    rw [salaminTail, ← tsum_div_const]
    exact tsum_congr fun i => by ring
  rw [salaminS, e1, e2]
  linarith

/-- The geometric tail bound: for `N ≥ 1`, `r_N ≤ (4/7) 2^N (a_N − b_N)²`.-/
theorem salaminTail_le {N : ℕ} (hN : 1 ≤ N) :
    salaminTail N ≤ 4 / 7 * 2 ^ N * (sA N - sB N) ^ 2 := by
  have hgap := salamin_gap_le_two_mul hN
  have hg0 : 0 ≤ sA N - sB N := sub_nonneg.mpr (agmB_le_agmA one_pos salaminB0_pos hN)
  have hterm : ∀ i : ℕ, 2 ^ (i + N + 1) * agmCsq 1 salaminB0 (i + N + 1)
      ≤ 2 ^ N / 2 * (sA N - sB N) ^ 2 * (1 / 8 : ℝ) ^ i := by
    intro i
    rw [agmCsq_succ one_pos salaminB0_pos]
    have h1 := agm_gap_add_le one_pos salaminB0_pos hN hgap i
    rw [add_comm N i] at h1
    have hgi : 0 ≤ sA (i + N) - sB (i + N) :=
      sub_nonneg.mpr (agmB_le_agmA one_pos salaminB0_pos (by omega))
    have h2 : ((sA (i + N) - sB (i + N)) / 2) ^ 2 ≤ ((sA N - sB N) / 4 ^ i / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc 2 ^ (i + N + 1) * ((sA (i + N) - sB (i + N)) / 2) ^ 2
        ≤ 2 ^ (i + N + 1) * ((sA N - sB N) / 4 ^ i / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ N / 2 * (sA N - sB N) ^ 2 * (1 / 8 : ℝ) ^ i := by
          rw [show (4 : ℝ) ^ i = 2 ^ i * 2 ^ i by rw [← mul_pow]; norm_num,
            show (1 / 8 : ℝ) ^ i = 1 / (2 ^ i * 2 ^ i * 2 ^ i) by
              rw [one_div_pow, ← mul_pow, ← mul_pow]; norm_num,
            pow_add, pow_add]
          field_simp
  have hsum : Summable fun i : ℕ => 2 ^ N / 2 * (sA N - sB N) ^ 2 * (1 / 8 : ℝ) ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc salaminTail N ≤ ∑' i : ℕ, 2 ^ N / 2 * (sA N - sB N) ^ 2 * (1 / 8 : ℝ) ^ i :=
        Summable.tsum_le_tsum hterm (summable_salaminTail N) hsum
    _ = 2 ^ N / 2 * (sA N - sB N) ^ 2 * (8 / 7) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
    _ = 4 / 7 * 2 ^ N * (sA N - sB N) ^ 2 := by ring

/-! ### Explicit convergence: how many steps for `w` bits

`a_1 − b_1 ≤ 1/64` and `b_1 > 2/3`, so `agm_gap_le` gives `a_n − b_n ≤ 8·2^(−8·2^(n−1))`, and
`|π_N − π| ≤ 7·2^N (a_N − b_N)² ≤ 2^(9+N−8·2^N) ≤ 2^(−w)` as soon as `w + N + 9 ≤ 8·2^N`;
`piSteps w = ⌊lg w⌋ + 1` steps suffice. -/

theorem salaminB0_bounds : (7071 / 10000 : ℝ) < salaminB0 ∧ salaminB0 < 70711 / 100000 := by
  have h0 := salaminB0_pos
  have h2 := salaminB0_sq
  constructor <;> nlinarith

theorem salamin_gap_one_le : sA 1 - sB 1 ≤ 1 / 64 := by
  obtain ⟨hlo, hhi⟩ := salaminB0_bounds
  rw [salamin_agmA_one]
  have hb1 : 0 ≤ sB 1 := (salamin_agm_pos 1).2.le
  have hsq := salamin_agmB_one_sq
  have : (8408 / 10000 : ℝ) ≤ sB 1 := by nlinarith
  linarith

/-- Quadratic convergence of the Brent–Salamin AGM: `a_n − b_n ≤ 8 · 2^(−8·2^(n−1))`.-/
theorem salamin_gap_le_pow {n : ℕ} (hn : 1 ≤ n) :
    sA n - sB n ≤ 8 * (1 / 2 : ℝ) ^ (8 * 2 ^ (n - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h := agm_gap_le one_pos salaminB0_pos j
  have hb1 := salamin_agmB_one_gt
  have hb1le : sB 1 ≤ 1 := (agmB_le_agmA one_pos salaminB0_pos le_rfl).trans (salamin_agmA_le_one le_rfl)
  have hg1 := salamin_gap_one_le
  have hg0 : 0 ≤ sA 1 - sB 1 := sub_nonneg.mpr (agmB_le_agmA one_pos salaminB0_pos le_rfl)
  have hratio : (sA 1 - sB 1) / (8 * sB 1) ≤ 1 / 256 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hratio0 : 0 ≤ (sA 1 - sB 1) / (8 * sB 1) := by positivity
  calc sA (j + 1) - sB (j + 1)
      ≤ 8 * sB 1 * ((sA 1 - sB 1) / (8 * sB 1)) ^ (2 ^ j) := h
    _ ≤ 8 * 1 * (1 / 256 : ℝ) ^ (2 ^ j) := by gcongr
    _ = 8 * (1 / 2 : ℝ) ^ (8 * 2 ^ j) := by
        rw [pow_mul, mul_one]; norm_num

/-- The number of Brent–Salamin steps for `w` bits: `⌊lg w⌋ + 1`.-/
def piSteps (w : ℕ) : ℕ := Nat.log 2 w + 1

theorem one_le_piSteps (w : ℕ) : 1 ≤ piSteps w := Nat.le_add_left 1 _

theorem piSteps_le (w : ℕ) (hw : 1 ≤ w) : piSteps w ≤ w := by
  unfold piSteps
  have := Nat.log_lt_of_lt_pow' (b := 2) (x := w) (y := w) (by omega) Nat.lt_two_pow_self
  omega

theorem piSteps_spec (w : ℕ) (hw : 1 ≤ w) : w + piSteps w + 9 ≤ 8 * 2 ^ piSteps w := by
  have h1 := Nat.lt_pow_succ_log_self (b := 2) one_lt_two w
  have h2 := piSteps_le w hw
  unfold piSteps at *
  omega

end BZ

end Azurite
