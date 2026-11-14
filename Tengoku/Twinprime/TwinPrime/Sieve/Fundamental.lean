/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author of the upstream development: Arend Mellendijk

Modified in this repository: ported to Lean / Mathlib v4.32.0 and adapted to
Mathlib's BoundingSieve definitions. See NOTICE for attribution.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The fundamental theorem of the Selberg upper-bound sieve

Mathlib (`Mathlib/NumberTheory/SelbergSieve.lean`) sets up bounding sieves, upper-bound (Λ²)
weights, and diagonalises the main term of a Λ² sieve.  This file completes the argument:

* `selbergBoundingSum` : `S = ∑_{l ∣ P, l² ≤ y} g(l)`;
* `selbergWeights`     : Selberg's optimal weights `γ_d`, with `γ_1 = 1` and `|γ_d| ≤ 1`;
* `mainSum (Λ² γ) = S⁻¹` exactly;
* `|μ⁺ d| ≤ 3^{ω d}` for the resulting upper-bound coefficients, vanishing for `d > y`;
* the **fundamental theorem** `selberg_bound_simple`:

  `siftedSum ≤ X / S + ∑_{d ∣ P, d ≤ y} 3^{ω d} |R_d|`.

This is a port to Mathlib `v4.32.0` of the corresponding development in Arend Mellendijk's
`selberg-sieve4` project (Apache 2.0), whose sieve setup was upstreamed into Mathlib.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-! ### Auxiliary sum manipulations -/

/-- Substituting `l = k * m` in a sum over divisors when the summand vanishes unless `k ∣ l`.
@isnad1 id=eq.1h3v.s6.e58a29820db4 from=translated src=- shape=c0e5fee2 vocab=74ce0c91
-/
theorem sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
    ∑ l ∈ n.divisors, f l = ∑ m ∈ n.divisors, if k * m ∣ n then f (k * m) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hk : k = 0
  · subst hk
    simp only [zero_mul, zero_dvd_iff, hn, ite_false, sum_const_zero]
    apply sum_eq_zero
    intro l hl
    exact h l (dvd_of_mem_divisors hl) (by
      rw [zero_dvd_iff]; exact (Nat.pos_of_mem_divisors hl).ne')
  have himage : (n.divisors.filter fun m => k * m ∣ n).image (fun m => k * m) =
      n.divisors.filter fun l => k ∣ l := by
    ext l
    simp only [mem_image, mem_filter, mem_divisors]
    constructor
    · rintro ⟨m, ⟨⟨-, -⟩, hkm⟩, rfl⟩
      exact ⟨⟨hkm, hn⟩, dvd_mul_right k m⟩
    · rintro ⟨⟨hl, -⟩, ⟨m, rfl⟩⟩
      exact ⟨m, ⟨⟨(dvd_mul_left m k).trans hl, hn⟩, hl⟩, rfl⟩
  rw [← sum_filter, ← sum_filter_add_sum_filter_not n.divisors (fun l => k ∣ l) f,
    sum_eq_zero (s := n.divisors.filter fun l => ¬ k ∣ l), add_zero, ← himage, sum_image]
  · intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) hxy
  · intro l hl
    rw [mem_filter] at hl
    exact h l (dvd_of_mem_divisors hl.1) hl.2

/-- `∑_{d ∣ n} μ d = [n = 1]`, as real numbers.
@isnad1 id=eq.0h1v.s6.2157276e1a40 from=translated src=- shape=2c947f87 vocab=f9192174
-/
theorem sum_divisors_moebius_real (n : ℕ) :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  have h' : ((∑ d ∈ n.divisors, μ d : ℤ) : ℝ) = ((if n = 1 then 1 else 0 : ℤ) : ℝ) := by
    rw [h]
  push_cast at h'
  exact h'

/-- For squarefree `m`: `∑_{d ∣ m, l ∣ d} μ d = [l = m] μ l`.
@isnad1 id=eq.1h2v.s6.9895b8ff2122 from=translated src=- shape=136fb774 vocab=bac52cb3
-/
theorem sum_moebius_dvd_eq (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d : ℝ) else 0) = if l = m then (μ l : ℝ) else 0 := by
  have hm0 : m ≠ 0 := hm.ne_zero
  by_cases hl : l ∣ m
  · obtain ⟨k, rfl⟩ := hl
    have hl0 : l ≠ 0 := by rintro rfl; simp at hm0
    have hcop : l.Coprime k := coprime_of_squarefree_mul hm
    have hk0 : k ≠ 0 := by rintro rfl; simp at hm0
    rw [sum_mul_subst l (l * k) (f := fun d => if l ∣ d then (μ d : ℝ) else 0)
      (by intro d _ hld; simp [hld])]
    have hstep : ∀ e ∈ (l * k).divisors,
        (if l * e ∣ l * k then (if l ∣ l * e then (μ (l * e) : ℝ) else 0) else 0) =
          if e ∣ k then (μ l : ℝ) * μ e else 0 := by
      intro e _
      by_cases h1 : e ∣ k
      · rw [ite_eq_left ((Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hl0)).mpr h1),
          ite_eq_left (dvd_mul_right l e), ite_eq_left h1,
          isMultiplicative_moebius.map_mul_of_coprime (hcop.coprime_dvd_right h1)]
        push_cast; ring
      · rw [ite_eq_right (fun h => h1 ((Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hl0)).mp h)),
          ite_eq_right h1]
    rw [sum_congr rfl hstep, ← sum_filter,
      Nat.divisors_filter_dvd_of_dvd hm0 (dvd_mul_left k l), ← mul_sum,
      sum_divisors_moebius_real]
    by_cases hk1 : k = 1
    · subst hk1; simp
    · rw [ite_eq_right hk1, ite_eq_right, mul_zero]
      intro h
      apply hk1
      have : l * k = l * 1 := by simpa using h.symm
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hl0) this
  · rw [ite_eq_right (by rintro rfl; exact hl dvd_rfl)]
    apply sum_eq_zero
    intro d hd
    rw [ite_eq_right]
    intro hld
    exact hl (hld.trans (dvd_of_mem_divisors hd))

/-- `∑_{d ∣ P, l ∣ d, d ∣ m} μ d = [l = m] μ l` for `m ∣ P`, `P` squarefree.
@isnad1 id=eq.2h3v.s6.e36d10072f2f from=translated src=- shape=d0402fdd vocab=bac52cb3
-/
theorem sum_moebius_dvd_dvd_eq {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  rw [← sum_moebius_dvd_eq l m (hP.squarefree_of_dvd hm),
    ← Nat.divisors_filter_dvd_of_dvd hP.ne_zero hm, sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases h1 : d ∣ m <;> by_cases h2 : l ∣ d <;> simp [h1, h2]

/-- Terms of a Λ² sieve vanish beyond the level when the weights vanish beyond `√y`.
@isnad1 id=eq.2h3v.s6.f28984b6fd93 from=translated src=- shape=5ecc3b30 vocab=54fd32c6
-/
theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬ (d : ℝ) ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬ (d : ℝ) ≤ y) :
    lambdaSquared w d = 0 := by
  unfold lambdaSquared
  apply sum_eq_zero
  intro d1 hd1
  apply sum_eq_zero
  intro d2 hd2
  split_ifs with h
  · -- one of `d1, d2` is at least `√d`, hence its square exceeds `y`.
    have hd1pos : 0 < d1 := Nat.pos_of_mem_divisors hd1
    have hd2pos : 0 < d2 := Nat.pos_of_mem_divisors hd2
    have hle : d ≤ d1 * d2 := by
      rw [h]
      exact Nat.le_of_dvd (Nat.mul_pos hd1pos hd2pos) (Nat.lcm_dvd_mul d1 d2)
    rcases le_total d1 d2 with hle' | hle'
    · rw [hw d2, mul_zero]
      intro hyp
      apply hd
      have : (d : ℝ) ≤ (d2 : ℝ) ^ 2 := by
        have h1 : (d : ℝ) ≤ (d1 : ℝ) * d2 := by exact_mod_cast hle
        have h2 : (d1 : ℝ) ≤ d2 := by exact_mod_cast hle'
        nlinarith [(d1.cast_nonneg : (0:ℝ) ≤ d1), (d2.cast_nonneg : (0:ℝ) ≤ d2)]
      linarith
    · rw [hw d1, zero_mul]
      intro hyp
      apply hd
      have : (d : ℝ) ≤ (d1 : ℝ) ^ 2 := by
        have h1 : (d : ℝ) ≤ (d1 : ℝ) * d2 := by exact_mod_cast hle
        have h2 : (d2 : ℝ) ≤ d1 := by exact_mod_cast hle'
        nlinarith [(d1.cast_nonneg : (0:ℝ) ≤ d1), (d2.cast_nonneg : (0:ℝ) ≤ d2)]
      linarith
  · rfl

end TwinPrime.Sieve

namespace SelbergSieve

open TwinPrime.Sieve

variable (s : SelbergSieve)

/-- `S = ∑_{l ∣ P, l² ≤ y} g(l)`, the sum controlling the main term.-/
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors s.prodPrimes, if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0

/--
@isnad1 id=lt.0h1v.s3.4947d8a62b52 from=translated src=- shape=b9369acb vocab=1b26df3f
-/
theorem selbergBoundingSum_pos : 0 < s.selbergBoundingSum := by
  unfold selbergBoundingSum
  rw [← sum_filter]
  apply sum_pos
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    exact selbergTerms_pos hl.1.1
  · refine ⟨1, ?_⟩
    rw [mem_filter, mem_divisors]
    refine ⟨⟨one_dvd _, prodPrimes_ne_zero⟩, ?_⟩
    simp [s.one_le_level]

/--
@isnad1 id=ne.0h1v.s3.732f4aaab975 from=translated src=- shape=a311c14d vocab=a641ac69
-/
theorem selbergBoundingSum_ne_zero : s.selbergBoundingSum ≠ 0 := s.selbergBoundingSum_pos.ne'

/--
@isnad1 id=le.0h1v.s3.bab673fa063b from=translated src=- shape=b9369acb vocab=ebc7b043
-/
theorem selbergBoundingSum_nonneg : 0 ≤ s.selbergBoundingSum := s.selbergBoundingSum_pos.le

/-- Selberg's optimal weights `γ_d`.-/
def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * s.selbergTerms d * μ d * (s.selbergBoundingSum)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes,
        if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
  else 0

/--
@isnad1 id=eq.1h2v.s4.fd520cd86a7d from=translated src=- shape=16b11ef8 vocab=661497b6
-/
theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ s.prodPrimes) :
    s.selbergWeights d = 0 := by
  rw [selbergWeights, ite_eq_right hd]

/--
@isnad1 id=eq.1h2v.s5.17ea5486f3ba from=translated src=- shape=1a3f1f1e vocab=d9435c0b
-/
theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬ (d : ℝ) ^ 2 ≤ s.level) :
    s.selbergWeights d = 0 := by
  unfold selbergWeights
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    intro m hm
    rw [ite_eq_right]
    rintro ⟨hyp, -⟩
    apply hd
    refine le_trans ?_ hyp
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_mem_divisors hm
    push_cast
    have : (d : ℝ) ≤ d * m := by nlinarith [(d.cast_nonneg : (0:ℝ) ≤ d)]
    exact pow_le_pow_left₀ (by positivity) this 2
  · rfl

/--
@isnad1 id=le.1h2v.s5.fa3a25d09527 from=translated src=- shape=7be01a52 vocab=20ea765e
-/
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ s.selbergWeights d * μ d := by
  unfold selbergWeights
  rw [ite_eq_left hdP]
  have hsum : 0 ≤ ∑ m ∈ divisors s.prodPrimes,
      if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0 := by
    apply sum_nonneg
    intro m hm
    split_ifs
    · exact (selbergTerms_pos (dvd_of_mem_divisors hm)).le
    · exact le_rfl
  have h1 : 0 ≤ (s.nu d)⁻¹ := (inv_pos.mpr (nu_pos_of_dvd_prodPrimes hdP)).le
  have h2 : 0 ≤ s.selbergTerms d := (selbergTerms_pos hdP).le
  have h3 : 0 ≤ (s.selbergBoundingSum)⁻¹ := (inv_pos.mpr s.selbergBoundingSum_pos).le
  have h4 : (0:ℝ) ≤ (μ d : ℝ) ^ 2 := sq_nonneg _
  have : (s.nu d)⁻¹ * s.selbergTerms d * (μ d : ℝ) * (s.selbergBoundingSum)⁻¹ *
      (∑ m ∈ divisors s.prodPrimes,
        if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0) *
      (μ d : ℝ) =
      (μ d : ℝ) ^ 2 * ((s.nu d)⁻¹ * s.selbergTerms d * (s.selbergBoundingSum)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes,
        if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0) := by
    ring
  rw [this]
  exact mul_nonneg h4 (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) hsum)

/-- The key identity: `ν d γ_d = S⁻¹ μ d ∑_{l ∣ P, d ∣ l, l² ≤ y} g l`.
@isnad1 id=eq.0h2v.s7.2b8bc6175b7a from=translated src=- shape=5e6c786c vocab=8e07c4f4
-/
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    s.nu d * s.selbergWeights d =
      (s.selbergBoundingSum)⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes,
          if d ∣ l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0 := by
  by_cases h_dvd : d ∣ s.prodPrimes
  swap
  · rw [selbergWeights_eq_zero_of_not_dvd s h_dvd, mul_zero, sum_eq_zero, mul_zero]
    intro l hl
    rw [ite_eq_right]
    rintro ⟨hdl, -⟩
    exact h_dvd (hdl.trans (dvd_of_mem_divisors hl))
  unfold selbergWeights
  rw [ite_eq_left h_dvd]
  -- change of variables `l = d * m` on the right-hand side
  rw [sum_mul_subst d s.prodPrimes (f := fun l =>
      if d ∣ l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0)
      (by intro l _ hdl; simp [hdl])]
  rw [mul_sum, mul_sum, mul_sum]
  apply sum_congr rfl
  intro m hm
  have hmP : m ∣ s.prodPrimes := dvd_of_mem_divisors hm
  -- `d * m ∣ P ↔ Coprime m d`
  have hiff : d * m ∣ s.prodPrimes ↔ m.Coprime d := by
    constructor
    · intro h
      exact (coprime_of_squarefree_mul (s.prodPrimes_squarefree.squarefree_of_dvd h)).symm
    · intro h
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h.symm h_dvd hmP
  by_cases hc : m.Coprime d
  · have hdm : d * m ∣ s.prodPrimes := hiff.mpr hc
    by_cases hy : ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level
    · rw [ite_eq_left hdm,
        ite_eq_left (show d ∣ d * m ∧ ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level from ⟨dvd_mul_right d m, hy⟩),
        ite_eq_left (show ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d from ⟨hy, hc⟩),
        selbergTerms_isMultiplicative.map_mul_of_coprime hc.symm]
      have hnu : s.nu d ≠ 0 := nu_ne_zero h_dvd
      field_simp
    · rw [ite_eq_left hdm,
        ite_eq_right (show ¬ (d ∣ d * m ∧ ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level) from fun h => hy h.2),
        ite_eq_right (show ¬ (((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d) from fun h => hy h.1)]
      ring
  · have hdm : ¬ d * m ∣ s.prodPrimes := fun h => hc (hiff.mp h)
    rw [ite_eq_right hdm,
      ite_eq_right (show ¬ (((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d) from fun h => hc h.2)]
    ring

/-- Diagonalisation: `∑_{d ∣ P, l ∣ d} ν d γ_d = [l² ≤ y] g l μ l S⁻¹`.
@isnad1 id=eq.1h2v.s7.e74cf7eada88 from=translated src=- shape=16e7fcaf vocab=340d4995
-/
theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * s.selbergWeights d else 0) =
      if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l * μ l * (s.selbergBoundingSum)⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * s.selbergWeights d else 0) =
        ∑ d ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
          if l ∣ d ∧ d ∣ k ∧ (k : ℝ) ^ 2 ≤ s.level then
            s.selbergTerms k * (s.selbergBoundingSum)⁻¹ * (μ d : ℝ) else 0 := by
      apply sum_congr rfl
      intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl
      intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
      intro _; ring
    _ = ∑ k ∈ divisors s.prodPrimes, if (k : ℝ) ^ 2 ≤ s.level then
            (∑ d ∈ divisors s.prodPrimes, if l ∣ d ∧ d ∣ k then (μ d : ℝ) else 0) *
              s.selbergTerms k * (s.selbergBoundingSum)⁻¹
          else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum]
      apply sum_congr rfl
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ← ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      · intro _; ring
    _ = if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l * μ l * (s.selbergBoundingSum)⁻¹
          else 0 := by
      rw [sum_eq_single_of_mem l hl]
      · rw [sum_moebius_dvd_dvd_eq s.prodPrimes_squarefree l l (dvd_of_mem_divisors hl),
          ite_eq_left rfl]
        split_ifs <;> ring
      · intro k hk hkl
        rw [sum_moebius_dvd_dvd_eq s.prodPrimes_squarefree l k (dvd_of_mem_divisors hk),
          ite_eq_right (Ne.symm hkl)]
        simp

/-- The Selberg upper-bound coefficients `μ⁺ = Λ² γ`.-/
def selbergMuPlus : ℕ → ℝ := lambdaSquared s.selbergWeights

/--
@isnad1 id=eq.0h1v.s4.2edf956d5ea7 from=translated src=- shape=59ae2d96 vocab=81067945
-/
theorem weight_one_of_selberg : s.selbergWeights 1 = 1 := by
  unfold selbergWeights
  rw [ite_eq_left (one_dvd _), s.nu_mult.left, selbergTerms_isMultiplicative.left]
  simp only [inv_one, mul_one, moebius_apply_one, Int.cast_one, one_mul, coprime_one_right_eq_true,
    and_true]
  change s.selbergBoundingSum⁻¹ * s.selbergBoundingSum = 1
  exact inv_mul_cancel₀ s.selbergBoundingSum_ne_zero

/--
@isnad1 id=eq.1h2v.s4.c8421381b202 from=translated src=- shape=cd68b033 vocab=2052ea7d
-/
theorem selbergMuPlus_eq_zero (d : ℕ) (hd : ¬ (d : ℝ) ≤ s.level) : s.selbergMuPlus d = 0 :=
  lambdaSquared_eq_zero_of_support _ s.level s.selbergWeights_eq_zero d hd

/--
@isnad1 id=isupperm.0h1v.s2.dd5a778eeb65 from=translated src=- shape=76a08d12 vocab=f997dc43
-/
theorem isUpperMoebius_selbergMuPlus : IsUpperMoebius s.selbergMuPlus :=
  upperMoebius_lambdaSquared s.selbergWeights s.weight_one_of_selberg

/-- The main term of the Selberg sieve is exactly `S⁻¹`.
@isnad1 id=eq.0h1v.s3.268f2a624d62 from=translated src=- shape=22861c53 vocab=9e5f6790
-/
theorem selberg_bound_simple_mainSum : s.mainSum s.selbergMuPlus = (s.selbergBoundingSum)⁻¹ := by
  unfold selbergMuPlus
  rw [mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc
    (∑ l ∈ divisors s.prodPrimes, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * s.selbergWeights d else 0) ^ 2) =
      ∑ l ∈ divisors s.prodPrimes,
        (if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0) * ((s.selbergBoundingSum)⁻¹) ^ 2 := by
      apply sum_congr rfl
      intro l hl
      rw [s.selbergWeights_diagonalisation l hl]
      split_ifs
      · have hg : s.selbergTerms l ≠ 0 := (selbergTerms_pos (dvd_of_mem_divisors hl)).ne'
        have hμ : ((μ l : ℝ)) ^ 2 = 1 := by
          have := moebius_sq_eq_one_of_squarefree (s.squarefree_of_mem_divisors_prodPrimes hl)
          exact_mod_cast this
        calc (s.selbergTerms l)⁻¹ * (s.selbergTerms l * μ l * (s.selbergBoundingSum)⁻¹) ^ 2
            = (s.selbergTerms l)⁻¹ * s.selbergTerms l * s.selbergTerms l * ((μ l : ℝ)) ^ 2 *
                ((s.selbergBoundingSum)⁻¹) ^ 2 := by ring
          _ = s.selbergTerms l * ((s.selbergBoundingSum)⁻¹) ^ 2 := by
                rw [inv_mul_cancel₀ hg, hμ]; ring
      · simp
    _ = (s.selbergBoundingSum)⁻¹ := by
      rw [← sum_mul]
      change s.selbergBoundingSum * (s.selbergBoundingSum⁻¹) ^ 2 = s.selbergBoundingSum⁻¹
      rw [sq, ← mul_assoc, mul_inv_cancel₀ s.selbergBoundingSum_ne_zero, one_mul]

/-! ### The bound `|γ_d| ≤ 1` -/

private theorem eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : m.Coprime d)
    (hk : k ≠ 0) : k = d.gcd (k * m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrd : r ∣ d := ⟨k, by rw [hr, mul_comm]⟩
  symm
  rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  exact Nat.Coprime.coprime_dvd_right hrd hmd

private theorem helper_iff {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors s.prodPrimes)
    (hm : m ∈ divisors s.prodPrimes) :
    k * m ∣ s.prodPrimes ∧ k = Nat.gcd d (k * m) ∧ ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ↔
      ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d := by
  have hk0 : k ≠ 0 := (Nat.pos_of_mem_divisors hk).ne'
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h3, ?_⟩
    obtain ⟨r, hr⟩ := hkd
    rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ hk0] at h2
    rw [hr, coprime_comm]
    apply Nat.Coprime.mul_left
    · exact coprime_of_squarefree_mul (s.prodPrimes_squarefree.squarefree_of_dvd h1)
    · exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, h1⟩
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Nat.Coprime.coprime_dvd_right hkd h2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h2 hk0

/--
@isnad1 id=le.1h2v.s5.825da01c5db6 from=translated src=- shape=37b444dd vocab=4962c221
-/
theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ s.selbergWeights d * (μ d : ℝ) * s.selbergBoundingSum := by
  have hP0 := s.prodPrimes_ne_zero
  calc
    s.selbergBoundingSum
      = ∑ k ∈ divisors s.prodPrimes, ∑ l ∈ divisors s.prodPrimes,
          if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0 := by
        unfold selbergBoundingSum
        rw [sum_comm]
        apply sum_congr rfl
        intro l _
        simp_rw [ite_and]
        have hmem : d.gcd l ∈ divisors s.prodPrimes := by
          rw [mem_divisors]; exact ⟨(Nat.gcd_dvd_left d l).trans hdP, hP0⟩
        rw [sum_ite_eq' (divisors s.prodPrimes) (d.gcd l), ite_eq_left hmem]
    _ = ∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            s.selbergTerms k * ∑ m ∈ divisors s.prodPrimes,
              if ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
          else 0 := by
        apply sum_congr rfl
        intro k hk
        rw [mul_sum]
        split_ifs with hkd
        swap
        · apply sum_eq_zero
          intro l _
          rw [ite_eq_right]
          rintro ⟨h, -⟩
          rw [h] at hkd
          exact hkd (Nat.gcd_dvd_left d l)
        rw [sum_mul_subst k s.prodPrimes (f := fun l =>
            if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0)]
        · apply sum_congr rfl
          intro m hm
          rw [mul_ite_zero, ← ite_and]
          apply if_ctx_congr _ _ fun _ => rfl
          · exact s.helper_iff hkd hk hm
          · intro h
            apply selbergTerms_isMultiplicative.right
            rw [coprime_comm]
            exact h.2.coprime_dvd_right hkd
        · intro l _ hkl
          apply ite_eq_right
          rintro ⟨h, -⟩
          rw [h] at hkl
          exact hkl (Nat.gcd_dvd_right d l)
    _ ≥ ∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            s.selbergTerms k * ∑ m ∈ divisors s.prodPrimes,
              if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
          else 0 := by
        apply sum_le_sum
        intro k _
        split_ifs with hkd
        swap
        · exact le_rfl
        apply mul_le_mul le_rfl _ _ (selbergTerms_pos (hkd.trans hdP)).le
        · apply sum_le_sum
          intro m hm
          split_ifs with h h' h'
          · exact le_rfl
          · exfalso
            apply h'
            refine ⟨?_, h.2⟩
            refine le_trans ?_ h.1
            have hkle : k ≤ d := Nat.le_of_dvd
              (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP0 hdP)) hkd
            have : ((k * m : ℕ) : ℝ) ≤ ((d * m : ℕ) : ℝ) := by
              exact_mod_cast Nat.mul_le_mul_right m hkle
            exact pow_le_pow_left₀ (by positivity) this 2
          · exact (selbergTerms_pos (dvd_of_mem_divisors hm)).le
          · exact le_rfl
        · apply sum_nonneg
          intro m hm
          split_ifs
          · exact (selbergTerms_pos (dvd_of_mem_divisors hm)).le
          · exact le_rfl
    _ = s.selbergWeights d * (μ d : ℝ) * s.selbergBoundingSum := by
        simp_rw [← ite_zero_mul]
        rw [← sum_mul, sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
        unfold selbergWeights
        rw [ite_eq_left hdP]
        have hμ : ((μ d : ℝ)) ^ 2 = 1 := by
          have := moebius_sq_eq_one_of_squarefree (s.prodPrimes_squarefree.squarefree_of_dvd hdP)
          exact_mod_cast this
        have hSS : s.selbergBoundingSum⁻¹ * s.selbergBoundingSum = 1 :=
          inv_mul_cancel₀ s.selbergBoundingSum_ne_zero
        set A := s.selbergTerms d * (s.nu d)⁻¹ *
          ∑ m ∈ divisors s.prodPrimes,
            if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0 with hA
        linear_combination (-A) * hμ - A * ((μ d : ℝ)) ^ 2 * hSS

/--
@isnad1 id=le.0h2v.s4.aa9b61501465 from=translated src=- shape=4884be87 vocab=6a7daa60
-/
theorem selberg_bound_weights (d : ℕ) : |s.selbergWeights d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp
  have h1 : s.selbergWeights d * (μ d : ℝ) * s.selbergBoundingSum ≤ 1 * s.selbergBoundingSum := by
    rw [one_mul]; exact s.selbergBoundingSum_ge hdP
  have h2 : s.selbergWeights d * (μ d : ℝ) ≤ 1 :=
    le_of_mul_le_mul_right h1 s.selbergBoundingSum_pos
  have habs : |(μ d : ℝ)| = 1 := by
    have := abs_moebius_eq_one_of_squarefree (s.prodPrimes_squarefree.squarefree_of_dvd hdP)
    exact_mod_cast this
  calc |s.selbergWeights d| = |s.selbergWeights d| * |(μ d : ℝ)| := by rw [habs, mul_one]
    _ = |s.selbergWeights d * (μ d : ℝ)| := (abs_mul _ _).symm
    _ = s.selbergWeights d * (μ d : ℝ) := abs_of_nonneg (s.selbergWeights_mul_mu_nonneg d hdP)
    _ ≤ 1 := h2

/--
@isnad1 id=le.1h2v.s6.14c6e27f2e1b from=translated src=- shape=150446ac vocab=0ca0392a
-/
theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors s.prodPrimes) :
    |s.selbergMuPlus n| ≤ (3 : ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z => if n = x.lcm z then 1 else 0
  unfold selbergMuPlus lambdaSquared
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
        if n = d1.lcm d2 then s.selbergWeights d1 * s.selbergWeights d2 else 0| ≤
      ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors,
        if n = d1.lcm d2 then s.selbergWeights d1 * s.selbergWeights d2 else 0| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
        |if n = d1.lcm d2 then s.selbergWeights d1 * s.selbergWeights d2 else 0| := by
        gcongr; exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := by
        gcongr with d1 _ d2
        simp only [f]
        split_ifs with h
        · rw [abs_mul]
          exact mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg _) (s.selberg_bound_weights d2)
        · simp
    _ = ∑ p ∈ n.divisors ×ˢ n.divisors, f p.1 p.2 := by rw [← Finset.sum_product']
    _ = ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.1.lcm p.2).card := by
        simp only [f]
        rw [← sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ((3 : ℕ) ^ ω n : ℕ) := by
        rw [← Nat.card_pair_lcm_eq (s.squarefree_of_mem_divisors_prodPrimes hn)]
        norm_cast
        apply congrArg
        ext p
        simp only [mem_filter]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩
    _ = (3 : ℝ) ^ ω n := by norm_num

/--
@isnad1 id=le.0h1v.s6.5e8309c29fbb from=translated src=- shape=5d403d3c vocab=4677438d
-/
theorem selberg_bound_simple_errSum :
    s.errSum s.selbergMuPlus ≤
      ∑ d ∈ divisors s.prodPrimes,
        if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0 := by
  unfold errSum
  apply sum_le_sum
  intro d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg _) (pow_nonneg (by norm_num) _)
    exact s.selberg_bound_muPlus d hd
  · rw [s.selbergMuPlus_eq_zero d h, abs_zero, zero_mul]

/-- **The fundamental theorem of the Selberg upper-bound sieve.**
@isnad1 id=le.0h1v.s6.7e17aa55a8bd from=translated src=- shape=3cef6c88 vocab=c67897e7
-/
theorem selberg_bound_simple :
    s.siftedSum ≤
      s.totalMass / s.selbergBoundingSum +
        ∑ d ∈ divisors s.prodPrimes,
          if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0 := by
  calc
    s.siftedSum ≤ s.totalMass * s.mainSum s.selbergMuPlus + s.errSum s.selbergMuPlus :=
      siftedSum_le_mainSum_errSum_of_upperMoebius _ s.isUpperMoebius_selbergMuPlus
    _ ≤ _ := by
      gcongr
      · rw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
      · exact s.selberg_bound_simple_errSum

end SelbergSieve
