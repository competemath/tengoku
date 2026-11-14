import Tengoku.Piirrationalitymeasure.Formalization.Denominator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The arithmetic step of Lemma 2.3, assuming the coefficient integrality and
local prime divisibility supplied by Lemmas 2.1 and 2.2. Only deleted primes
that divide the index are required to divide the coefficient.
-/

namespace PiIrrationality

/--
@isnad1 id=dvd.3h3v.s6.957e8aca70d2 from=translated src=- shape=c1d82fcc vocab=7f016b03
-/
theorem reducedLcmNat_clears_of_local_divisibility
    (n j q : ℕ) (hj0 : j ≠ 0) (hjbound : j ≤ 7430 * n)
    (hq : ∀ p : ℕ, removablePrime n p → p ∣ j → p ∣ q) :
    j ∣ reducedLcmNat n * q := by
  classical
  have hjL : j ∣ lcmRange (7430 * n) :=
    dvd_lcmRange _ _ (Nat.one_le_iff_ne_zero.mpr hj0) hjbound
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
  intro p k hp hpkj
  by_cases hk0 : k = 0
  · simp [hk0]
  have hpj : p ∣ j := (dvd_pow_self p hk0).trans hpkj
  by_cases hrem : removablePrime n p
  · have hklt : k < 2 := by
      by_contra hk
      have hp2j : p ^ 2 ∣ j :=
        (pow_dvd_pow p (by omega : 2 ≤ k)).trans hpkj
      have hp2le := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hp2j
      have hp2gt := removablePrime_square_gt n p hrem
      omega
    have hk1 : k = 1 := by omega
    simpa [hk1] using dvd_mul_of_dvd_right (hq p hrem hpj) (reducedLcmNat n)
  · have hcop : Nat.Coprime (p ^ k) (Phi n) := by
      unfold Phi
      apply Nat.Coprime.prod_right
      intro r hr
      have hrrem : removablePrime n r := (Finset.mem_filter.mp hr).2
      have hpr : p ≠ r := by
        intro heq
        exact hrem (heq ▸ hrrem)
      exact ((Nat.coprime_primes hp hrrem.1).2 hpr).pow_left k
    have hpkL : p ^ k ∣ reducedLcmNat n * Phi n := by
      rw [reducedLcmNat_mul_Phi]
      exact hpkj.trans hjL
    exact dvd_mul_of_dvd_left (hcop.dvd_of_dvd_mul_right hpkL) q

/--
@isnad1 id=dvd.3h3v.s6.d446b73d13e5 from=translated src=- shape=ce630fa0 vocab=a2f56021
-/
theorem reducedLcmNat_clears_int_of_local_divisibility
    (n : ℕ) (j q : ℤ) (hj0 : j ≠ 0) (hjbound : j.natAbs ≤ 7430 * n)
    (hq : ∀ p : ℕ, removablePrime n p → (p : ℤ) ∣ j → (p : ℤ) ∣ q) :
    j ∣ (reducedLcmNat n : ℤ) * q := by
  have hnat : j.natAbs ∣ reducedLcmNat n * q.natAbs := by
    apply reducedLcmNat_clears_of_local_divisibility n j.natAbs q.natAbs
      (Int.natAbs_ne_zero.mpr hj0) hjbound
    intro p hp hpj
    exact Int.natCast_dvd.mp (hq p hp (Int.natCast_dvd.mpr hpj))
  apply Int.natAbs_dvd_natAbs.mp
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact hnat

/--
@isnad1 id=eq.0h1v.s3.694014ca99d5 from=translated src=- shape=6b4ab8ce vocab=7a420395
-/
theorem reducedLcm_eq_natCast (n : ℕ) :
    reducedLcm n = (reducedLcmNat n : ℚ) := by
  have hPhi : (Phi n : ℚ) ≠ 0 := by exact_mod_cast (Phi_pos n).ne'
  unfold reducedLcm
  symm
  apply (eq_div_iff hPhi).2
  exact_mod_cast reducedLcmNat_mul_Phi n

/--
@isnad1 id=ex.3h3v.s6.778ab5f75ff8 from=translated src=- shape=79cafd42 vocab=4f975aba
-/
theorem reducedLcm_mul_div_is_integer
    (n : ℕ) (j q : ℤ) (hj0 : j ≠ 0) (hjbound : j.natAbs ≤ 7430 * n)
    (hq : ∀ p : ℕ, removablePrime n p → (p : ℤ) ∣ j → (p : ℤ) ∣ q) :
    ∃ z : ℤ, reducedLcm n * (q : ℚ) / (j : ℚ) = (z : ℚ) := by
  obtain ⟨z, hz⟩ := reducedLcmNat_clears_int_of_local_divisibility
    n j q hj0 hjbound hq
  refine ⟨z, ?_⟩
  rw [reducedLcm_eq_natCast]
  have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0
  apply (div_eq_iff hjQ).2
  exact_mod_cast (hz.trans (mul_comm j z))

/--
@isnad1 id=dvd.1h2v.s4.99f9dec1e384 from=translated src=- shape=537bf8a9 vocab=7dc4f922
-/
theorem Phi_dvd_int_of_local_divisibility
    (n : ℕ) (q : ℤ)
    (hq : ∀ p : ℕ, removablePrime n p → (p : ℤ) ∣ q) :
    (Phi n : ℤ) ∣ q := by
  classical
  have hpair : (removablePrimes n : Set ℕ).Pairwise
      (fun p r => IsCoprime (p : ℤ) (r : ℤ)) := by
    intro p hp r hr hpr
    have hpprime := (Finset.mem_filter.mp hp).2.1
    have hrprime := (Finset.mem_filter.mp hr).2.1
    exact ((Nat.coprime_primes hpprime hrprime).2 hpr).isCoprime
  have hprod : (∏ p ∈ removablePrimes n, (p : ℤ)) ∣ q :=
    Finset.prod_dvd_of_coprime hpair
      (fun p hp => hq p (Finset.mem_filter.mp hp).2)
  simpa [Phi] using hprod

/--
@isnad1 id=ex.1h2v.s5.45ec7c1a0f4c from=translated src=- shape=f4008bb0 vocab=706ecd40
-/
theorem div_Phi_is_integer
    (n : ℕ) (q : ℤ)
    (hq : ∀ p : ℕ, removablePrime n p → (p : ℤ) ∣ q) :
    ∃ z : ℤ, (q : ℚ) / (Phi n : ℚ) = (z : ℚ) := by
  obtain ⟨z, hz⟩ := Phi_dvd_int_of_local_divisibility n q hq
  refine ⟨z, ?_⟩
  apply (div_eq_iff (by exact_mod_cast (Phi_pos n).ne' : (Phi n : ℚ) ≠ 0)).2
  exact_mod_cast (hz.trans (mul_comm (Phi n : ℤ) z))

/--
@isnad1 id=ex.4h3v.s7.3acf87f972c3 from=translated src=- shape=c6d74037 vocab=dc09b54e
-/
theorem reducedLcm_clears_laurent_range
    (n : ℕ) (j q : ℤ)
    (hjlo : -(7430 * (n : ℤ)) + 1 ≤ j) (hjhi : j ≤ 5570 * (n : ℤ))
    (hj0 : j ≠ 0)
    (hq : ∀ p : ℕ, removablePrime n p → (p : ℤ) ∣ j → (p : ℤ) ∣ q) :
    ∃ z : ℤ, reducedLcm n * (q : ℚ) / (j : ℚ) = (z : ℚ) := by
  apply reducedLcm_mul_div_is_integer n j q hj0 _ hq
  have habs : |j| ≤ (7430 * (n : ℤ)) := abs_le.mpr ⟨by omega, by omega⟩
  rw [Int.abs_eq_natAbs] at habs
  exact_mod_cast habs

/--
@isnad1 id=and.3h2v.s8.7747f634c6d3 from=translated src=- shape=c74c7993 vocab=60f7e18f
-/
theorem reducedLcm_laurent_integrality_of_coefficients
    (n : ℕ) (hn : 0 < n) (c : ℤ → ℚ)
    (hintegral : ∀ j : ℤ, -(7430 * (n : ℤ)) + 1 ≤ j → j ≤ 5570 * (n : ℤ) →
      ∃ q : ℤ, (10 : ℚ) ^ (-j) * c j = (q : ℚ))
    (hlocal : ∀ j : ℤ, -(7430 * (n : ℤ)) + 1 ≤ j → j ≤ 5570 * (n : ℤ) →
      ∀ p : ℕ, removablePrime n p → (p : ℤ) ∣ j →
        (p : ℤ) ∣ ((10 : ℚ) ^ (-j) * c j).num) :
    (∃ L : ℤ, reducedLcm n = (L : ℚ)) ∧
      (∀ j : ℤ, -(7430 * (n : ℤ)) + 1 ≤ j → j ≤ 5570 * (n : ℤ) → j ≠ 0 →
        ∃ z : ℤ, reducedLcm n * ((10 : ℚ) ^ (-j) * c j) / (j : ℚ) = (z : ℚ)) ∧
      (∃ z : ℤ, c 0 / (Phi n : ℚ) = (z : ℚ)) := by
  refine ⟨⟨(reducedLcmNat n : ℤ), ?_⟩, ?_, ?_⟩
  · simpa only [Int.cast_natCast] using reducedLcm_eq_natCast n
  · intro j hjlo hjhi hj0
    obtain ⟨q, hq⟩ := hintegral j hjlo hjhi
    rw [hq]
    apply reducedLcm_clears_laurent_range n j q hjlo hjhi hj0
    intro p hp hpj
    simpa only [hq, Rat.num_intCast] using hlocal j hjlo hjhi p hp hpj
  · have hlo : -(7430 * (n : ℤ)) + 1 ≤ 0 := by omega
    have hhi : (0 : ℤ) ≤ 5570 * (n : ℤ) := by positivity
    obtain ⟨q, hq⟩ := hintegral 0 hlo hhi
    have hc0 : c 0 = (q : ℚ) := by simpa using hq
    rw [hc0]
    apply div_Phi_is_integer n q
    intro p hp
    simpa [hc0] using hlocal 0 hlo hhi p hp (dvd_zero _)

/--
@isnad1 id=coprime.0h1v.s3.ef4b23655c1d from=translated src=- shape=082ff3f3 vocab=26e1aeb2
-/
theorem Phi_coprime_ten (n : ℕ) : Nat.Coprime (Phi n) 10 := by
  classical
  unfold Phi
  apply Nat.Coprime.prod_left
  intro p hp
  have hrem : removablePrime n p := (Finset.mem_filter.mp hp).2
  have hc2 : Nat.Coprime p 2 :=
    (Nat.coprime_primes hrem.1 (by norm_num)).2 (by have := hrem.2.1; omega)
  have hc5 : Nat.Coprime p 5 :=
    (Nat.coprime_primes hrem.1 (by norm_num)).2 (by have := hrem.2.1; omega)
  simpa using hc2.mul_right hc5

/--
@isnad1 id=ex.3h3v.s6.a4c2fbc8a3f7 from=translated src=- shape=e2566854 vocab=fd2e55d2
-/
theorem rational_integer_of_coprime_multipliers
    (x : ℚ) (a b : ℕ) (hab : Nat.Coprime a b)
    (ha : ∃ u : ℤ, (a : ℚ) * x = (u : ℚ))
    (hb : ∃ v : ℤ, (b : ℚ) * x = (v : ℚ)) :
    ∃ z : ℤ, x = (z : ℚ) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  obtain ⟨s, t, hst⟩ := hab.isCoprime
  have hstQ : (s : ℚ) * (a : ℚ) + (t : ℚ) * (b : ℚ) = 1 := by
    exact_mod_cast hst
  refine ⟨s * u + t * v, ?_⟩
  calc
    x = ((s : ℚ) * (a : ℚ) + (t : ℚ) * (b : ℚ)) * x := by rw [hstQ, one_mul]
    _ = (s : ℚ) * ((a : ℚ) * x) + (t : ℚ) * ((b : ℚ) * x) := by ring
    _ = ((s * u + t * v : ℤ) : ℚ) := by rw [hu, hv]; push_cast; ring

/--
@isnad1 id=ex.2h2v.s6.df93c1e8f208 from=translated src=- shape=f1889c4a vocab=0313f3e3
-/
theorem integer_of_Phi_and_ten_power
    (n : ℕ) (x : ℚ)
    (hPhi : ∃ u : ℤ, (Phi n : ℚ) * x = (u : ℚ))
    (hten : ∃ k : ℕ, ∃ v : ℤ, (10 : ℚ) ^ k * x = (v : ℚ)) :
    ∃ z : ℤ, x = (z : ℚ) := by
  obtain ⟨k, v, hv⟩ := hten
  apply rational_integer_of_coprime_multipliers x (Phi n) (10 ^ k)
    ((Phi_coprime_ten n).pow_right k) hPhi
  exact ⟨v, by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hv⟩

end PiIrrationality
