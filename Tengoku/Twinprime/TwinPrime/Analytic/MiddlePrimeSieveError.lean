import Tengoku.Twinprime.TwinPrime.Analytic.LargePrimeModuli
import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieveDenominator
import Tengoku.Twinprime.TwinPrime.Analytic.SquarefreeWeightedDistribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Aggregating the actual middle-prime Selberg remainder

Every modulus is squarefree and has a unique largest prime. This preserves
the Selberg weight and embeds the complete error in the squarefree-weighted
progression sum, to which the proved weighted distribution theorem applies.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace TwinPrime.Analytic

open TwinPrime.Sieve

def middlePrimeSieveErrorMass (U W Y : ℕ) (z : ℕ → ℕ) : ℝ :=
  ∑ q ∈ (Ioc U W).filter Nat.Prime,
    ∑ d ∈ (oddPrimorial (z q)).divisors.filter (fun d => d ≤ z q ^ 2),
      (3 : ℝ) ^ ω d * progressionMaxError Y (q * d)

/--
@isnad1 id=le.0h4v.s4.23586476dca0 from=translated src=- shape=457952fd vocab=79b6a651
-/
theorem middlePrimeSieveErrorMass_nonneg (U W Y : ℕ) (z : ℕ → ℕ) :
    0 ≤ middlePrimeSieveErrorMass U W Y z :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    mul_nonneg (by positivity) (progressionMaxError_nonneg _ _)

/-- The entire remainder is embedded into one squarefree weighted error
sum. In particular no replacement of `3^ω(d)` by a constant occurs.
@isnad1 id=le.2h5v.s6.e78cd267a53d from=translated src=- shape=a584818f vocab=b2514e2d
-/
theorem middlePrimeSieveErrorMass_le_weighted (U W D Y : ℕ) (z : ℕ → ℕ)
    (hU : 2 ≤ U)
    (hz : ∀ q ∈ Ioc U W, q.Prime → z q < q ∧ q * z q ^ 2 ≤ D) :
    middlePrimeSieveErrorMass U W Y z ≤
      squarefreeWeightedProgressionError (oddPrimorial D) D Y := by
  classical
  let E : ℕ → ℝ := fun m =>
    if m ∣ oddPrimorial D then (3 : ℝ) ^ ω m * progressionMaxError Y m else 0
  have hE : ∀ m, 0 ≤ E m := by
    intro m
    dsimp [E]
    split_ifs
    · exact mul_nonneg (by positivity) (progressionMaxError_nonneg Y m)
    · exact le_rfl
  have hinner (q : ℕ) (hqmem : q ∈ (Ioc U W).filter Nat.Prime) :
      (∑ d ∈ (oddPrimorial (z q)).divisors.filter (fun d => d ≤ z q ^ 2),
        (3 : ℝ) ^ ω d * progressionMaxError Y (q * d)) ≤
        ∑ d ∈ (Icc 1 (D / q)).filter
          (fun d => ∀ p, Nat.Prime p → p ∣ d → p < q), E (q * d) := by
    obtain ⟨hqI, hq⟩ := mem_filter.mp hqmem
    obtain ⟨hzq, hlevel⟩ := hz q hqI hq
    have hqodd : Odd q := hq.odd_of_ne_two (by have := (mem_Ioc.mp hqI).1; omega)
    have hsub : (oddPrimorial (z q)).divisors.filter (fun d => d ≤ z q ^ 2) ⊆
        (Icc 1 (D / q)).filter (fun d => ∀ p, Nat.Prime p → p ∣ d → p < q) := by
      intro d hd
      obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, ?_⟩, ?_⟩
      · apply (Nat.le_div_iff_mul_le hq.pos).mpr
        simpa only [mul_comm] using (Nat.mul_le_mul_left q hdz).trans hlevel
      · intro p hp hpd
        exact (((prime_dvd_oddPrimorial_iff hp).mp
          (hpd.trans (Nat.dvd_of_mem_divisors hdP))).2).trans_lt hzq
    calc
      _ ≤ ∑ d ∈ (oddPrimorial (z q)).divisors.filter (fun d => d ≤ z q ^ 2),
          E (q * d) := by
        apply sum_le_sum
        intro d hd
        obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
        have hdiv := Nat.dvd_of_mem_divisors hdP
        have hqd := prime_coprime_of_dvd_oddPrimorial q (z q) d hq hzq hdiv
        have hdodd : Odd d := Nat.not_even_iff_odd.mp
          (fun h => not_two_dvd_of_dvd_oddPrimorial hdiv h.two_dvd)
        have hsq : Squarefree (q * d) := (Nat.squarefree_mul hqd).mpr
          ⟨hq.squarefree, (oddPrimorial_squarefree (z q)).squarefree_of_dvd hdiv⟩
        have hle : q * d ≤ D := (Nat.mul_le_mul_left q hdz).trans hlevel
        have hmP := dvd_oddPrimorial_of_odd_squarefree_le (q * d) D
          (hqodd.mul hdodd) hsq hle
        dsimp [E]
        rw [ite_eq_left hmP]
        apply mul_le_mul_of_nonneg_right _ (progressionMaxError_nonneg Y (q * d))
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
        rw [cardDistinctFactors_mul hqd, cardDistinctFactors_apply_prime hq]
        omega
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hE (q * d))
  calc
    _ ≤ ∑ q ∈ (Ioc U W).filter Nat.Prime,
        ∑ d ∈ (Icc 1 (D / q)).filter
          (fun d => ∀ p, Nat.Prime p → p ∣ d → p < q), E (q * d) :=
      sum_le_sum hinner
    _ ≤ ∑ m ∈ Icc 1 D, E m :=
      sum_largest_prime_modulus_multiples_le U W D E (fun m _ => hE m)
    _ = _ := by
      dsimp only [E, squarefreeWeightedProgressionError]
      rw [← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext m
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hm1, hmD⟩, hmP⟩
        exact ⟨⟨hmP, oddPrimorial_ne_zero D⟩, hmD⟩
      · rintro ⟨⟨hmP, _⟩, hmD⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hmP
          (Nat.pos_of_ne_zero (oddPrimorial_ne_zero D)), hmD⟩, hmP⟩

end TwinPrime.Analytic
