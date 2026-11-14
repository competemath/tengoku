/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author of the upstream development: Arend Mellendijk

Modified in this repository: ported to Lean / Mathlib v4.32.0 and adapted to
the current divisor-sum APIs. See NOTICE for attribution.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Divisor sums with `k^{ω(d)}` weights

For squarefree `P` and `k : ℕ`,

* `sum_pow_cardDistinctFactors_div_self_le_log_pow` :
  `∑_{d ∣ P, d ≤ x} k^{ω d} / d ≤ (1 + log x)^k`;
* `sum_pow_cardDistinctFactors_le_self_mul_log_pow` :
  `∑_{d ∣ P, d ≤ x} k^{ω d} ≤ x (1 + log x)^k`.

These control the error term of the Selberg sieve once `|R_d| ≤ 2^{ω d}` (giving `6^{ω d}` after
multiplying by the `3^{ω d}` from the fundamental theorem).  The proof is Lemma 3.1 in
Heath-Brown's sieve notes: `k^{ω d}` counts the ordered factorisations `d = a_1 ⋯ a_k` of a
squarefree `d` (Mathlib's `Nat.card_finMulAntidiag_of_squarefree`), so the sum unfolds into a
`k`-fold product of harmonic-type sums.  Ported from Mellendijk's `selberg-sieve4`.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-- `∑_{d ∣ P, d ≤ x} 1/d ≤ 1 + log x`.
@isnad1 id=le.1h2v.s6.d186e383676a from=translated src=- shape=8be54f0d vocab=8094b088
-/
theorem sum_divisors_inv_le_one_add_log {P : ℕ} (x : ℝ) (hx : 1 ≤ x) :
    (∑ d ∈ P.divisors, if (d : ℝ) ≤ x then (d : ℝ)⁻¹ else 0) ≤ 1 + Real.log x := by
  rw [← sum_filter]
  calc (∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) ≤ x), (d : ℝ)⁻¹)
      ≤ ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (d : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [mem_filter] at hd
          rw [mem_Icc]
          exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hd.2⟩
        · intro d _ _
          positivity
    _ = (harmonic ⌊x⌋₊ : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ 1 + Real.log x := harmonic_floor_le_one_add_log x hx

/-- Lemma 3.1 in Heath-Brown's notes: `∑_{d ∣ P, d ≤ x} k^{ω d} / d ≤ (1 + log x)^k`.
@isnad1 id=le.2h3v.s7.289cfdc3efd5 from=translated src=- shape=7b1f86f7 vocab=fd20f1ba
-/
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if (d : ℝ) ≤ x then (k : ℝ) ^ (ω d) / (d : ℝ) else 0)
      ≤ (1 + Real.log x) ^ k := by
  have hP0 : P ≠ 0 := hP.ne_zero
  -- the "cost" of a divisor `d`
  set c : ℕ → ℝ := fun d => if (d : ℝ) ≤ x then (d : ℝ)⁻¹ else 0 with hc
  have hc_nonneg : ∀ d, 0 ≤ c d := by
    intro d; simp only [hc]; split_ifs <;> positivity
  calc
    (∑ d ∈ P.divisors, if (d : ℝ) ≤ x then (k : ℝ) ^ (ω d) / (d : ℝ) else 0)
        = ∑ d ∈ P.divisors, ∑ a ∈ Fintype.piFinset fun _ : Fin k => P.divisors,
            if ∏ i, a i = d then c d else 0 := by
          apply sum_congr rfl
          intro d hd
          have hdP : d ∣ P := dvd_of_mem_divisors hd
          rw [← sum_filter, sum_const, nsmul_eq_mul,
            ← Nat.finMulAntidiag_eq_piFinset_divisors_filter hdP hP0,
            Nat.card_finMulAntidiag_of_squarefree (hP.squarefree_of_dvd hdP)]
          simp only [hc]
          split_ifs
          · push_cast; ring
          · simp
    _ = ∑ a ∈ Fintype.piFinset fun _ : Fin k => P.divisors,
          if ∏ i, a i ∈ P.divisors then c (∏ i, a i) else 0 := by
          rw [sum_comm]
          apply sum_congr rfl
          intro a _
          rw [sum_ite_eq P.divisors (∏ i, a i) c]
    _ ≤ ∑ a ∈ Fintype.piFinset fun _ : Fin k => P.divisors,
          if ((∏ i, a i : ℕ) : ℝ) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := by
          apply sum_le_sum
          intro a _
          split_ifs with h1 h2 h2
          · simp only [hc, ite_eq_left h2]
            push_cast
            rw [prod_inv_distrib]
          · simp only [hc, ite_eq_right h2]; exact le_rfl
          · exact prod_nonneg fun i _ => by positivity
          · exact le_rfl
    _ ≤ ∑ a ∈ Fintype.piFinset fun _ : Fin k => P.divisors,
          ∏ i, if ((a i : ℕ) : ℝ) ≤ x then (a i : ℝ)⁻¹ else 0 := by
          apply sum_le_sum
          intro a ha
          rw [Fintype.mem_piFinset] at ha
          split_ifs with h
          · apply le_of_eq
            apply prod_congr rfl
            intro i _
            rw [ite_eq_left]
            refine le_trans ?_ h
            have hpos : ∀ j, 0 < a j := fun j => Nat.pos_of_mem_divisors (ha j)
            have : a i ≤ ∏ j, a j := by
              rw [← Finset.prod_erase_mul _ _ (mem_univ i)]
              exact Nat.le_mul_of_pos_left _ (prod_pos fun j _ => hpos j)
            exact_mod_cast this
          · exact prod_nonneg fun i _ => by split_ifs <;> positivity
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if (d : ℝ) ≤ x then (d : ℝ)⁻¹ else 0 := by
          rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if (d : ℝ) ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
          rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k :=
          pow_le_pow_left₀ (sum_nonneg fun d _ => by split_ifs <;> positivity)
            (sum_divisors_inv_le_one_add_log x hx) k

/-- `∑_{d ∣ P, d ≤ x} k^{ω d} ≤ x (1 + log x)^k`.
@isnad1 id=le.2h3v.s6.2896f5de7be9 from=translated src=- shape=b726adf4 vocab=701282ba
-/
theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if (d : ℝ) ≤ x then (k : ℝ) ^ (ω d) else 0)
      ≤ x * (1 + Real.log x) ^ k := by
  calc
    (∑ d ∈ P.divisors, if (d : ℝ) ≤ x then (k : ℝ) ^ (ω d) else 0)
        ≤ ∑ d ∈ P.divisors, x * (if (d : ℝ) ≤ x then (k : ℝ) ^ (ω d) / (d : ℝ) else 0) := by
          apply sum_le_sum
          intro d hd
          split_ifs with h
          · have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
            rw [mul_div_assoc', le_div_iff₀ hdpos]
            have : (0 : ℝ) ≤ (k : ℝ) ^ (ω d) := by positivity
            nlinarith
          · simp
    _ = x * ∑ d ∈ P.divisors, (if (d : ℝ) ≤ x then (k : ℝ) ^ (ω d) / (d : ℝ) else 0) := by
          rw [mul_sum]
    _ ≤ x * (1 + Real.log x) ^ k :=
          mul_le_mul_of_nonneg_left (sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP)
            (by linarith)

end TwinPrime.Sieve
