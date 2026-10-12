/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Pippenger expander construction (Lemma 4.1)

This file isolates the Pippenger probabilistic construction from Section 4 of
the companion paper. It provides:

1. A `PippengerRowCertificate` structure capturing the hypotheses of Lemma 4.1.
2. Four row-specific numerical certificates (E₁–E₄).
3. Row-specific probabilistic/counting constructions for E₁–E₄.
4. The combined `pippenger_required_expanders` theorem.

**Reference**: Section 4 and the table in Section 5 of
the companion paper.
-/
module

public import Tengoku.LeanPool.LeanPool.KaltonRoberts.PippengerProof
import Tengoku.LeanPool.LeanPool.KaltonRoberts.Numerical
import Tengoku.LeanPool.LeanPool.KaltonRoberts.PhiAnalysis
public import Tengoku

/-!
# Pippenger expander construction

Row certificates and row-specific constructions for the probabilistic expander
argument used in the Kalton-Roberts bound.
-/

@[expose] public section

namespace KaltonRoberts

open Finset BigOperators

/-! ## Row certificate structure -/

/-- A `PippengerRowCertificate` captures exactly the hypotheses of Lemma 4.1
for one row of the expander table. Given parameters `α r θ c δ`, it asserts:
- Range conditions: `0 < α < θ < 1`, `3 ≤ r`, `r < c`, `θ = r/c`
- Tail bound: `e² · θ^{1−r} · δ^{r−2} < 1/20`
- Entropy negativity: `Φ_{r,θ}(x) < 0` for all `x ∈ [δ, α]`

The paper uses `c = r/θ`. For the four rows:
- E₁: r = 4, θ = 1/3, c = 12
- E₂: r = 4, θ = 4/7, c = 7
- E₃: r = 4, θ = 2/7, c = 14
- E₄: r = 5, θ = 5/11, c = 11
-/
structure PippengerRowCertificate (α : ℚ) (r : ℕ) (θ : ℚ) (c : ℕ) (δ : ℚ) : Prop where
  /-- `0 < α` -/
  α_pos : (0 : ℚ) < α
  /-- `α < θ` -/
  α_lt_θ : α < θ
  /-- `θ < 1` -/
  θ_lt_one : θ < 1
  /-- `3 ≤ r` -/
  r_ge_three : 3 ≤ r
  /-- `r < c` -/
  r_lt_c : r < c
  /-- `θ = r / c` (in ℚ) -/
  θ_eq : θ = (r : ℚ) / (c : ℚ)
  /-- `0 < δ` -/
  δ_pos : (0 : ℚ) < δ
  /-- `δ < α` -/
  δ_lt_α : δ < α
  /-- Tail bound (real): `e² · (θ : ℝ)^{1−r} · (δ : ℝ)^{r−2} < 1/20` -/
  tail_bound : Real.exp 2 * (θ : ℝ) ^ (1 - (r : ℤ)) * (δ : ℝ) ^ ((r : ℤ) - 2) < 1 / 20
  /-- Entropy negativity: `Φ_{r,θ}(x) < 0` for all `x ∈ [δ, α]` -/
  phi_neg : ∀ x : ℝ, (δ : ℝ) ≤ x → x ≤ (α : ℝ) → Phi (r : ℝ) (θ : ℝ) x < 0

/-! ## Tail bound proofs -/

/-- Tail bound for E₁: `e² · (1/3)^{-3} · (1/100)^2 < 1/20` -/
theorem tail_bound_real_E₁ :
    Real.exp 2 * ((1 / 3 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) * ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) < 1 / 20 :=
      by
  have he := e_sq_lt
  have h1 : ((1 / 3 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) = 27 := by
    push_cast; norm_num [zpow_neg, zpow_natCast]
  have h2 : ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) = 1 / 10000 := by
    push_cast; norm_num [zpow_natCast]
  rw [h1, h2]; nlinarith

/-- Tail bound for E₂: `e² · (4/7)^{-3} · (1/100)^2 < 1/20` -/
theorem tail_bound_real_E₂ :
    Real.exp 2 * ((4 / 7 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) * ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) < 1 / 20 :=
      by
  have he := e_sq_lt
  have h1 : ((4 / 7 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) = (7 / 4 : ℝ) ^ (3 : ℕ) := by
    push_cast; norm_num [zpow_neg, zpow_natCast, inv_eq_one_div]
  have h2 : ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) = 1 / 10000 := by
    push_cast; norm_num [zpow_natCast]
  rw [h1, h2]
  have h3 : (7 / 4 : ℝ) ^ (3 : ℕ) = 343 / 64 := by norm_num
  rw [h3]; nlinarith

/-- Tail bound for E₃: `e² · (2/7)^{-3} · (1/100)^2 < 1/20` -/
theorem tail_bound_real_E₃ :
    Real.exp 2 * ((2 / 7 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) * ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) < 1 / 20 :=
      by
  have he := e_sq_lt
  have h1 : ((2 / 7 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) = (7 / 2 : ℝ) ^ (3 : ℕ) := by
    push_cast; norm_num [zpow_neg, zpow_natCast, inv_eq_one_div]
  have h2 : ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) = 1 / 10000 := by
    push_cast; norm_num [zpow_natCast]
  rw [h1, h2]
  have h3 : (7 / 2 : ℝ) ^ (3 : ℕ) = 343 / 8 := by norm_num
  rw [h3]; nlinarith

/-- Tail bound for E₄: `e² · (5/11)^{-4} · (1/100)^3 < 1/20` -/
theorem tail_bound_real_E₄ :
    Real.exp 2 * ((5 / 11 : ℚ) : ℝ) ^ (1 - (5 : ℤ)) * ((1 / 100 : ℚ) : ℝ) ^ ((5 : ℤ) - 2) < 1 / 20
      := by
  have he := e_sq_lt
  have h1 : ((5 / 11 : ℚ) : ℝ) ^ (1 - (5 : ℤ)) = (11 / 5 : ℝ) ^ (4 : ℕ) := by
    push_cast; norm_num [zpow_neg, zpow_natCast, inv_eq_one_div]
  have h2 : ((1 / 100 : ℚ) : ℝ) ^ ((5 : ℤ) - 2) = 1 / 1000000 := by
    push_cast; norm_num [zpow_natCast]
  rw [h1, h2]
  have h3 : (11 / 5 : ℝ) ^ (4 : ℕ) = 14641 / 625 := by norm_num
  rw [h3]; nlinarith

/-! ## Phi negativity on intervals

For each Pippenger row, the proof combines:
1. endpoint log certificates from `LogBounds.lean`,
2. derivative and convexity facts from `PhiDeriv.lean`, and
3. the endpoint-maximum property for convex functions.

**Reference**: Section 4 of the companion paper.
-/

/-! ## Row certificates -/

/-! ## Row-specific bad-ratio estimates -/

theorem tail_bound_E₁_simplified :
    Real.exp 2 * 27 * ((1 / 100 : ℝ) ^ 2) < 1 / 20 := by
  have h := tail_bound_real_E₁
  norm_num at h ⊢
  exact h

theorem small_term_E₁
    (N L m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (hmL : m ≤ L)
    (hNL : 4 * N = 12 * L) (hLreal : (L : ℝ) = (1 / 3 : ℝ) * (N : ℝ))
    (hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((12 * m).choose (4 * m) : ℝ) / ((4 * N).choose (4 * m) : ℝ)
      ≤ ((1 / 20 : ℝ) ^ m) := by
  have hcmN : 12 * m ≤ 4 * N := by
    simp_all
  have hraw := pippenger_small_term_raw N L 4 12 m hm hmN hmL (by norm_num) hcmN
  refine le_trans hraw ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbase_eq :
      (Real.exp 1 * (N : ℝ) / (m : ℝ) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((12 * m : ℕ) : ℝ) / ((4 * N : ℕ) : ℝ)) ^ 4)
        =
      Real.exp 2 * 27 * (((m : ℝ) / (N : ℝ)) ^ 2) := by
    rw [hLreal]
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    norm_num [Nat.cast_mul]
    field_simp [hm_ne, hN_ne]
    ring
  have hx_nonneg : 0 ≤ (m : ℝ) / (N : ℝ) := by positivity
  have hx2_le : ((m : ℝ) / (N : ℝ)) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hx_nonneg hsmall 2
  have hbase_le : Real.exp 2 * 27 * (((m : ℝ) / (N : ℝ)) ^ 2) ≤ 1 / 20 := by
    have hcoef_nonneg : 0 ≤ Real.exp 2 * 27 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx2_le hcoef_nonneg
    nlinarith [tail_bound_E₁_simplified, hmul]
  rw [hbase_eq]
  exact pow_le_pow_left₀ (by positivity) hbase_le m

theorem tail_bound_E₂_simplified :
    Real.exp 2 * ((7 / 4 : ℝ) ^ 3) * ((1 / 100 : ℝ) ^ 2) < 1 / 20 := by
  have h := tail_bound_real_E₂
  norm_num at h ⊢
  exact h

theorem small_term_E₂
    (N L m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (hmL : m ≤ L)
    (hNL : 4 * N = 7 * L) (hLreal : (L : ℝ) = (4 / 7 : ℝ) * (N : ℝ))
    (hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((7 * m).choose (4 * m) : ℝ) / ((4 * N).choose (4 * m) : ℝ)
      ≤ ((1 / 20 : ℝ) ^ m) := by
  have hcmN : 7 * m ≤ 4 * N := by
    simp_all
  have hraw := pippenger_small_term_raw N L 4 7 m hm hmN hmL (by norm_num) hcmN
  refine le_trans hraw ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbase_eq :
      (Real.exp 1 * (N : ℝ) / (m : ℝ) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((7 * m : ℕ) : ℝ) / ((4 * N : ℕ) : ℝ)) ^ 4)
        =
      Real.exp 2 * ((7 / 4 : ℝ) ^ 3) * (((m : ℝ) / (N : ℝ)) ^ 2) := by
    rw [hLreal]
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    norm_num [Nat.cast_mul]
    field_simp [hm_ne, hN_ne]
    ring
  have hx_nonneg : 0 ≤ (m : ℝ) / (N : ℝ) := by positivity
  have hx2_le : ((m : ℝ) / (N : ℝ)) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hx_nonneg hsmall 2
  have hbase_le : Real.exp 2 * ((7 / 4 : ℝ) ^ 3) *
      (((m : ℝ) / (N : ℝ)) ^ 2) ≤ 1 / 20 := by
    have hcoef_nonneg : 0 ≤ Real.exp 2 * ((7 / 4 : ℝ) ^ 3) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx2_le hcoef_nonneg
    nlinarith [tail_bound_E₂_simplified, hmul]
  rw [hbase_eq]
  exact pow_le_pow_left₀ (by positivity) hbase_le m

theorem tail_bound_E₃_simplified :
    Real.exp 2 * ((7 / 2 : ℝ) ^ 3) * ((1 / 100 : ℝ) ^ 2) < 1 / 20 := by
  have h := tail_bound_real_E₃
  norm_num at h ⊢
  exact h

theorem small_term_E₃
    (N L m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (hmL : m ≤ L)
    (hNL : 4 * N = 14 * L) (hLreal : (L : ℝ) = (2 / 7 : ℝ) * (N : ℝ))
    (hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((14 * m).choose (4 * m) : ℝ) / ((4 * N).choose (4 * m) : ℝ)
      ≤ ((1 / 20 : ℝ) ^ m) := by
  have hcmN : 14 * m ≤ 4 * N := by
    simp_all
  have hraw := pippenger_small_term_raw N L 4 14 m hm hmN hmL (by norm_num) hcmN
  refine le_trans hraw ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbase_eq :
      (Real.exp 1 * (N : ℝ) / (m : ℝ) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((14 * m : ℕ) : ℝ) / ((4 * N : ℕ) : ℝ)) ^ 4)
        =
      Real.exp 2 * ((7 / 2 : ℝ) ^ 3) * (((m : ℝ) / (N : ℝ)) ^ 2) := by
    rw [hLreal]
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    norm_num [Nat.cast_mul]
    field_simp [hm_ne, hN_ne]
    ring
  have hx_nonneg : 0 ≤ (m : ℝ) / (N : ℝ) := by positivity
  have hx2_le : ((m : ℝ) / (N : ℝ)) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hx_nonneg hsmall 2
  have hbase_le : Real.exp 2 * ((7 / 2 : ℝ) ^ 3) *
      (((m : ℝ) / (N : ℝ)) ^ 2) ≤ 1 / 20 := by
    have hcoef_nonneg : 0 ≤ Real.exp 2 * ((7 / 2 : ℝ) ^ 3) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx2_le hcoef_nonneg
    nlinarith [tail_bound_E₃_simplified, hmul]
  rw [hbase_eq]
  exact pow_le_pow_left₀ (by positivity) hbase_le m

theorem tail_bound_E₄_simplified :
    Real.exp 2 * ((11 / 5 : ℝ) ^ 4) * ((1 / 100 : ℝ) ^ 3) < 1 / 20 := by
  have h := tail_bound_real_E₄
  norm_num at h ⊢
  exact h

theorem small_term_E₄
    (N L m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (hmL : m ≤ L)
    (hNL : 5 * N = 11 * L) (hLreal : (L : ℝ) = (5 / 11 : ℝ) * (N : ℝ))
    (hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((11 * m).choose (5 * m) : ℝ) / ((5 * N).choose (5 * m) : ℝ)
      ≤ ((1 / 20 : ℝ) ^ m) := by
  have hcmN : 11 * m ≤ 5 * N := by
    simp_all
  have hraw := pippenger_small_term_raw N L 5 11 m hm hmN hmL (by norm_num) hcmN
  refine le_trans hraw ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbase_eq :
      (Real.exp 1 * (N : ℝ) / (m : ℝ) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((11 * m : ℕ) : ℝ) / ((5 * N : ℕ) : ℝ)) ^ 5)
        =
      Real.exp 2 * ((11 / 5 : ℝ) ^ 4) * (((m : ℝ) / (N : ℝ)) ^ 3) := by
    rw [hLreal]
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    norm_num [Nat.cast_mul]
    field_simp [hm_ne, hN_ne]
    ring
  have hx_nonneg : 0 ≤ (m : ℝ) / (N : ℝ) := by positivity
  have hx3_le : ((m : ℝ) / (N : ℝ)) ^ 3 ≤ (1 / 100 : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ hx_nonneg hsmall 3
  have hbase_le : Real.exp 2 * ((11 / 5 : ℝ) ^ 4) *
      (((m : ℝ) / (N : ℝ)) ^ 3) ≤ 1 / 20 := by
    have hcoef_nonneg : 0 ≤ Real.exp 2 * ((11 / 5 : ℝ) ^ 4) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx3_le hcoef_nonneg
    nlinarith [tail_bound_E₄_simplified, hmul]
  rw [hbase_eq]
  exact pow_le_pow_left₀ (by positivity) hbase_le m

/-! ## Combined expander existence -/

end KaltonRoberts
