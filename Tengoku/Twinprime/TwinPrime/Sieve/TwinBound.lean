import Tengoku
import Tengoku.Twinprime.TwinPrime.Basic
import Tengoku.Twinprime.TwinPrime.Sieve.TwinSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sieve bound for the twin prime counting function

Combining the fundamental theorem of the Selberg sieve (`selberg_bound_simple`) with the twin
sieve data (`twinSieve`), the remainder bound `|R_d| ≤ 2^{ω d}`, the error-sum estimate, and the
Mertens-free lower bound for `S`, we obtain for every `z ≥ 16`:

  `π₂(x) ≤ (z + 1) + (x + 1) / L(z)² + z² (1 + log z²)^6`,   `L(z) = ¼ log z − ½ log 2 > 0`.

The parameter `z` is chosen in `TwinPrime/Brun.lean`.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

namespace TwinPrime

/-- The number of twin primes `p ≤ x` (lower members of pairs).-/
def twinCount (x : ℕ) : ℕ := #{p ∈ range (x + 1) | p ∈ twinPrimes}

namespace Sieve

/-! ### `π₂(x) ≤ z + 1 + siftedSum` -/

/--
@isnad1 id=coprime.2h2v.s4.b63ba7c49e67 from=translated src=- shape=8d576c2e vocab=34477ffb
-/
theorem coprime_oddPrimorial_of_prime_gt {z p : ℕ} (hp : p.Prime) (hzp : z < p) :
    Nat.Coprime (oddPrimorial z) p := by
  unfold oddPrimorial
  apply Nat.Coprime.prod_left
  intro q hq
  rw [mem_erase, mem_primesLE] at hq
  rw [Nat.coprime_primes hq.2.2 hp]
  omega

/-! ### The completely multiplicative function `2^{Ω n} / n` -/

/-- `twinF n = 2^{Ω n} / n` (and `0` at `0`): completely multiplicative, agrees with `twinNu`
on primes.-/
def twinF : ℕ →* ℝ where
  toFun n := if n = 0 then 0 else (2 : ℝ) ^ (Ω n) / n
  map_one' := by simp
  map_mul' := by
    intro m n
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [mul_eq_zero, hm, hn, or_self, ite_false]
    rw [cardFactors_mul hm hn, pow_add]
    push_cast
    field_simp

/--
@isnad1 id=eq.0h1v.s6.2213f0bc1a9f from=translated src=- shape=4ee2b9bf vocab=0df67be5
-/
theorem twinF_apply' (n : ℕ) : twinF n = if n = 0 then 0 else (2 : ℝ) ^ (Ω n) / n := rfl

/--
@isnad1 id=eq.1h1v.s6.1b6625ab4252 from=translated src=- shape=526cba0d vocab=2da2e61b
-/
theorem twinF_apply {n : ℕ} (hn : n ≠ 0) : twinF n = (2 : ℝ) ^ (Ω n) / n := by
  rw [twinF_apply', ite_eq_right hn]

/--
@isnad1 id=le.0h1v.s5.709c51236fb9 from=translated src=- shape=904cabbd vocab=d896fd08
-/
theorem twinF_nonneg (n : ℕ) : 0 ≤ twinF n := by
  rw [twinF_apply']
  split_ifs <;> positivity

/--
@isnad1 id=eq.1h1v.s5.13ba5069f62f from=translated src=- shape=f1017915 vocab=3b212d73
-/
theorem twinF_prime {p : ℕ} (hp : p.Prime) : twinF p = twinNu p := by
  rw [twinF_apply hp.ne_zero, twinNu_prime hp, cardFactors_apply_prime hp, pow_one]

/-- `#divisors m ≤ 2^{Ω m}`.
@isnad1 id=le.0h1v.s5.8c577eb9b485 from=translated src=- shape=77aceaa7 vocab=31d78d82
-/
theorem card_divisors_le_two_pow_cardFactors (m : ℕ) : #m.divisors ≤ 2 ^ (Ω m) := by
  induction m using Nat.recOnPrimePow with
  | zero => simp
  | one => simp
  | prime_pow_mul a p n hp hpa hn ih =>
    have ha : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
    rw [Nat.Coprime.card_divisors_mul
        ((Nat.coprime_pow_left_iff hn p a).mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa)),
      ← sigma_zero_apply (p ^ n), sigma_zero_apply_prime_pow hp,
      cardFactors_mul (pow_ne_zero n hp.ne_zero) ha, cardFactors_apply_prime_pow hp, pow_add]
    exact Nat.mul_le_mul Nat.lt_two_pow_self ih

/-- `(∑_{a ∈ A} 1/a)² ≤ ∑_{m ∈ T} 2^{Ω m}/m` whenever `A · A ⊆ T`.
@isnad1 id=le.2h2v.s7.c66abbbfb132 from=translated src=- shape=0a2af44a vocab=389d8851
-/
theorem sq_sum_inv_le_sum_twinF (A T : Finset ℕ) (hA0 : ∀ a ∈ A, a ≠ 0)
    (hAT : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ T) :
    (∑ a ∈ A, (a : ℝ)⁻¹) ^ 2 ≤ ∑ m ∈ T, twinF m := by
  classical
  calc (∑ a ∈ A, (a : ℝ)⁻¹) ^ 2 = ∑ q ∈ A ×ˢ A, ((q.1 * q.2 : ℕ) : ℝ)⁻¹ := by
        rw [sq, sum_mul_sum, ← sum_product']
        apply sum_congr rfl
        intro q _
        push_cast
        rw [mul_inv]
    _ = ∑ m ∈ T, ∑ q ∈ A ×ˢ A with q.1 * q.2 = m, ((q.1 * q.2 : ℕ) : ℝ)⁻¹ :=
        (sum_fiberwise_of_maps_to (fun q hq => by
          rw [mem_product] at hq; exact hAT _ hq.1 _ hq.2) _).symm
    _ = ∑ m ∈ T, (#{q ∈ A ×ˢ A | q.1 * q.2 = m} : ℝ) * (m : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro m _
        rw [sum_congr rfl (g := fun _ => (m : ℝ)⁻¹) (fun q hq => by
            rw [mem_filter] at hq
            rw [hq.2]), sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ T, twinF m := by
        apply sum_le_sum
        intro m _
        by_cases hm0 : m = 0
        · rw [twinF_apply', ite_eq_left hm0]
          have : {q ∈ A ×ˢ A | q.1 * q.2 = m} = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro q hq
            rw [mem_product] at hq
            rw [hm0]
            exact mul_ne_zero (hA0 _ hq.1) (hA0 _ hq.2)
          rw [this, card_empty]
          simp
        rw [twinF_apply hm0, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc (#{q ∈ A ×ˢ A | q.1 * q.2 = m} : ℝ) ≤ #m.divisors := by
              apply Nat.cast_le.mpr
              apply card_le_card_of_injOn (fun q => q.1)
              · intro q hq
                simp only [coe_filter, Set.mem_ofPred_eq, mem_product] at hq
                rw [mem_coe, mem_divisors]
                exact ⟨Dvd.intro _ hq.2, hm0⟩
              · intro q hq q' hq' heq
                simp only [coe_filter, Set.mem_ofPred_eq, mem_product] at hq hq'
                simp only at heq
                ext
                · exact heq
                · have h1 : q.1 * q.2 = q.1 * q'.2 := by rw [hq.2, ← hq'.2, heq]
                  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hA0 _ hq.1.1)) h1
          _ ≤ 2 ^ (Ω m) := by exact_mod_cast card_divisors_le_two_pow_cardFactors m

/-! ### Harmonic sums over odd integers -/

/-- The odd integers in `[1, w]`.-/
def oddUpTo (w : ℕ) : Finset ℕ := (Finset.Icc 1 w).filter fun a => ¬ 2 ∣ a

/--
@isnad1 id=iff.0h2v.s5.057925da5b3e from=translated src=- shape=1801dbe8 vocab=51e7cb12
-/
theorem mem_oddUpTo {w a : ℕ} : a ∈ oddUpTo w ↔ (1 ≤ a ∧ a ≤ w) ∧ ¬ 2 ∣ a := by
  unfold oddUpTo
  rw [mem_filter, mem_Icc]

/-- `∑_{a ≤ w, a odd} 1/a ≥ ½ log (w/2 + 1)`.
@isnad1 id=le.0h1v.s6.18a295206b5c from=translated src=- shape=c59022f8 vocab=0d516b33
-/
theorem sum_inv_oddUpTo_ge (w : ℕ) :
    (1 / 2 : ℝ) * Real.log ((w : ℝ) / 2 + 1) ≤ ∑ a ∈ oddUpTo w, (a : ℝ)⁻¹ := by
  set K := (w + 1) / 2 with hK
  have h1 : ∑ k ∈ Finset.Icc 1 K, ((2 * k - 1 : ℕ) : ℝ)⁻¹ ≤ ∑ a ∈ oddUpTo w, (a : ℝ)⁻¹ := by
    rw [← sum_image (f := fun a : ℕ => (a : ℝ)⁻¹) (g := fun k : ℕ => 2 * k - 1)
      (fun k hk k' hk' h => by
        rw [Finset.mem_coe, mem_Icc] at hk hk'
        simp only at h
        omega)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro a ha
      rw [mem_image] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      rw [mem_Icc] at hk
      rw [mem_oddUpTo]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      have h2k := (Nat.le_div_iff_mul_le two_pos).mp hk.2
      omega
    · intros; positivity
  have h2 : ∑ k ∈ Finset.Icc 1 K, ((2 * k : ℕ) : ℝ)⁻¹ ≤
      ∑ k ∈ Finset.Icc 1 K, ((2 * k - 1 : ℕ) : ℝ)⁻¹ := by
    apply sum_le_sum
    intro k hk
    rw [mem_Icc] at hk
    apply inv_anti₀
    · exact_mod_cast (by omega : 0 < 2 * k - 1)
    · exact_mod_cast (by omega : 2 * k - 1 ≤ 2 * k)
  have h3 : ∑ k ∈ Finset.Icc 1 K, ((2 * k : ℕ) : ℝ)⁻¹ = (1 / 2 : ℝ) * (harmonic K : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [mul_inv]
    ring
  have h4 : Real.log ((K : ℝ) + 1) ≤ harmonic K := by
    have := log_add_one_le_harmonic K
    push_cast at this
    exact this
  have h5 : Real.log ((w : ℝ) / 2 + 1) ≤ Real.log ((K : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    have hwK : w ≤ 2 * K := by
      have := Nat.div_add_mod (w + 1) 2
      have hmod : (w + 1) % 2 < 2 := Nat.mod_lt _ two_pos
      omega
    have : (w : ℝ) ≤ 2 * K := by exact_mod_cast hwK
    linarith
  calc (1 / 2 : ℝ) * Real.log ((w : ℝ) / 2 + 1)
      ≤ (1 / 2) * Real.log ((K : ℝ) + 1) := mul_le_mul_of_nonneg_left h5 (by norm_num)
    _ ≤ (1 / 2) * harmonic K := mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = ∑ k ∈ Finset.Icc 1 K, ((2 * k : ℕ) : ℝ)⁻¹ := h3.symm
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ((2 * k - 1 : ℕ) : ℝ)⁻¹ := h2
    _ ≤ ∑ a ∈ oddUpTo w, (a : ℝ)⁻¹ := h1

/-! ### The lower bound for the Selberg sum of the twin sieve -/

/--
@isnad1 id=le.1h2v.s5.7d81deae6c9d from=translated src=- shape=2aa84f35 vocab=71ab6dcf
-/
theorem twinSieve_boundingSum_ge_sq (x z : ℕ) (hz : 1 ≤ z) :
    (∑ a ∈ oddUpTo (Nat.sqrt z), (a : ℝ)⁻¹) ^ 2 ≤ (twinSieve x z hz).selbergBoundingSum := by
  refine le_trans (sq_sum_inv_le_sum_twinF (oddUpTo (Nat.sqrt z)) (oddUpTo z) ?_ ?_) ?_
  · intro a ha
    rw [mem_oddUpTo] at ha
    omega
  · intro a ha b hb
    rw [mem_oddUpTo] at ha hb ⊢
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega)), ?_⟩, ?_⟩
    · calc a * b ≤ Nat.sqrt z * Nat.sqrt z := Nat.mul_le_mul ha.1.2 hb.1.2
        _ ≤ z := Nat.sqrt_le z
    · intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
      · exact ha.2 h
      · exact hb.2 h
  · apply SelbergSieve.selbergBoundingSum_ge_sum _ twinF twinF_nonneg
    · intro p hp _
      exact twinF_prime hp
    · intro m hm
      rw [mem_oddUpTo] at hm
      omega
    · intro m hm p hp hpm
      rw [mem_oddUpTo] at hm
      rw [twinSieve_prodPrimes, prime_dvd_oddPrimorial_iff hp]
      constructor
      · rintro rfl
        exact hm.2 hpm
      · exact le_trans (Nat.le_of_dvd (by omega) hpm) hm.1.2
    · intro m hm
      rw [mem_oddUpTo] at hm
      rw [twinSieve_level]
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hm.1.2) 2

/-- `L(z) = ¼ log z − ½ log 2`.-/
def Lz (z : ℕ) : ℝ := (1 / 4 : ℝ) * Real.log z - (1 / 2 : ℝ) * Real.log 2

/--
@isnad1 id=lt.1h1v.s4.c8e74efc8992 from=translated src=- shape=f8216502 vocab=cb061e6e
-/
theorem Lz_pos {z : ℕ} (hz : 16 ≤ z) : 0 < Lz z := by
  unfold Lz
  have h16 : Real.log 16 ≤ Real.log z := Real.log_le_log (by norm_num) (by exact_mod_cast hz)
  have : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/--
@isnad1 id=le.1h1v.s5.4312b7648a53 from=translated src=- shape=9bb901cc vocab=e9082a5d
-/
theorem Lz_le_sum_inv_oddUpTo {z : ℕ} (hz : 1 ≤ z) :
    Lz z ≤ ∑ a ∈ oddUpTo (Nat.sqrt z), (a : ℝ)⁻¹ := by
  refine le_trans ?_ (sum_inv_oddUpTo_ge (Nat.sqrt z))
  unfold Lz
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz
  have hsqrt : Real.sqrt z < (Nat.sqrt z : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast Nat.lt_succ_sqrt' z
  have hsqrt_pos : 0 < Real.sqrt z := Real.sqrt_pos.mpr hzpos
  have hlog : Real.log (Real.sqrt z / 2) ≤ Real.log ((Nat.sqrt z : ℝ) / 2 + 1) := by
    apply Real.log_le_log (by positivity)
    linarith
  have : Real.log (Real.sqrt z / 2) = (1 / 2 : ℝ) * Real.log z - Real.log 2 := by
    rw [Real.log_div hsqrt_pos.ne' (by norm_num), Real.log_sqrt hzpos.le]
    ring
  linarith

/--
@isnad1 id=le.1h2v.s5.b8546ec85eec from=translated src=- shape=a4a94fff vocab=c1447c51
-/
theorem twinSieve_boundingSum_ge (x z : ℕ) (hz : 16 ≤ z) :
    (Lz z) ^ 2 ≤ (twinSieve x z (by omega)).selbergBoundingSum := by
  refine le_trans ?_ (twinSieve_boundingSum_ge_sq x z (by omega))
  exact pow_le_pow_left₀ (Lz_pos hz).le (Lz_le_sum_inv_oddUpTo (by omega)) 2

/-! ### The error sum -/

/--
@isnad1 id=le.1h2v.s7.1d07d136bdb0 from=translated src=- shape=c8d1cbe2 vocab=785790a4
-/
theorem twinSieve_errSum_le (x z : ℕ) (hz : 1 ≤ z) :
    (∑ d ∈ (oddPrimorial z).divisors,
        if (d : ℝ) ≤ (z : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(twinSieve x z hz).rem d| else 0)
      ≤ (z : ℝ) ^ 2 * (1 + Real.log ((z : ℝ) ^ 2)) ^ 6 := by
  calc (∑ d ∈ (oddPrimorial z).divisors,
          if (d : ℝ) ≤ (z : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(twinSieve x z hz).rem d| else 0)
      ≤ ∑ d ∈ (oddPrimorial z).divisors,
          if (d : ℝ) ≤ (z : ℝ) ^ 2 then ((6 : ℕ) : ℝ) ^ ω d else 0 := by
        apply sum_le_sum
        intro d hd
        split_ifs
        · have h := twinSieve_abs_rem_le x z hz (dvd_of_mem_divisors hd)
          calc (3 : ℝ) ^ ω d * |(twinSieve x z hz).rem d| ≤ (3 : ℝ) ^ ω d * 2 ^ ω d :=
                mul_le_mul_of_nonneg_left h (by positivity)
            _ = ((6 : ℕ) : ℝ) ^ ω d := by rw [← mul_pow]; norm_num
        · exact le_rfl
    _ ≤ (z : ℝ) ^ 2 * (1 + Real.log ((z : ℝ) ^ 2)) ^ 6 := by
        apply sum_pow_cardDistinctFactors_le_self_mul_log_pow
        · have : (1 : ℝ) ≤ z := by exact_mod_cast hz
          nlinarith
        · exact oddPrimorial_squarefree z

/-! ### The explicit sieve bound -/

end Sieve

end TwinPrime
