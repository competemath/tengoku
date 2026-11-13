import Tengoku.Rankamplificationtotient.RankAmplification.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Prime providers for Euler's totient This file formalizes the elementary provider extraction used in Section 3 of *Rank Amplification for Shifted Equal Values of Euler's Totient Function*. -/

namespace RankAmplification

/-- A natural prime dividing a finite product divides one of its factors.-/
theorem exists_mem_dvd_finset_prod_of_prime {p : ℕ} (hp : p.Prime) {ι : Type*}
    (s : Finset ι) (f : ι → ℕ) (h : p ∣ ∏ a ∈ s, f a) :
    ∃ a ∈ s, p ∣ f a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (hp.not_dvd_one (by simpa using h)).elim
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha] at h
      rcases hp.dvd_mul.mp h with hfa | hrest
      · exact ⟨a, Finset.mem_insert_self a s, hfa⟩
      · obtain ⟨b, hbs, hfb⟩ := ih hrest
        exact ⟨b, Finset.mem_insert_of_mem hbs, hfb⟩

/-- A prime divisor is bounded by the largest-prime-factor convention used in the paper.-/
theorem prime_le_largestPrimeFactor {q m : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hqm : q ∣ m) :
    q ≤ largestPrimeFactor m := by
  have hmem : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqm, hm⟩
  have hsup : q ≤ m.primeFactors.sup id := by
    simpa using (Finset.le_sup (f := id) hmem)
  exact hsup.trans (Nat.le_max_right 1 _)

/-- Above the convention value `1`, the largest prime factor belongs to the prime support.-/
theorem largestPrimeFactor_mem_primeFactors {m : ℕ} (hlarge : 1 < largestPrimeFactor m) :
    largestPrimeFactor m ∈ m.primeFactors := by
  have hsup : 1 < m.primeFactors.sup id := by
    rw [largestPrimeFactor] at hlarge
    simpa only [lt_max_iff, lt_self_iff_false, false_or] using hlarge
  have hnonempty : m.primeFactors.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsup
    simp at hsup
  obtain ⟨q, hqmem, hqeq⟩ := Finset.exists_mem_eq_sup m.primeFactors hnonempty id
  rw [largestPrimeFactor, Nat.max_eq_right hsup.le, hqeq]
  exact hqmem

/-- Above the convention value, `largestPrimeFactor m` is prime.-/
theorem largestPrimeFactor_prime {m : ℕ} (hlarge : 1 < largestPrimeFactor m) :
    (largestPrimeFactor m).Prime :=
  Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem_primeFactors hlarge)

/-- Above the convention value, `largestPrimeFactor m` divides `m`.-/
theorem largestPrimeFactor_dvd {m : ℕ} (hlarge : 1 < largestPrimeFactor m) :
    largestPrimeFactor m ∣ m :=
  Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem_primeFactors hlarge)

/-- Smoothness bounds the largest prime factor, including the paper's convention at `1`.-/
theorem largestPrimeFactor_le_of_isSmooth {y m : ℕ} (hy : 1 ≤ y) (hm : IsSmooth y m) :
    largestPrimeFactor m ≤ y := by
  rw [largestPrimeFactor, Nat.max_le]
  exact ⟨hy, Finset.sup_le fun q hq ↦ hm.2 q hq⟩

/-- If primes `p` and `q` satisfy `p ∣ q - 1`, then `p < q`.-/
theorem prime_lt_of_dvd_pred {p q : ℕ} (_hp : p.Prime) (hq : q.Prime) (h : p ∣ q - 1) :
    p < q := by
  have hpred : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
  have hle : p ≤ q - 1 := Nat.le_of_dvd hpred h
  omega

/-- A provider congruence can be written with a positive multiplier.-/
theorem exists_pos_mul_add_one_eq_of_dvd_pred {p q : ℕ} (_hp : p.Prime) (hq : q.Prime)
    (h : p ∣ q - 1) : ∃ k : ℕ, 0 < k ∧ q = k * p + 1 := by
  obtain ⟨k, hk⟩ := h
  have hkpos : 0 < k := by
    by_contra hknot
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hknot
    subst k
    simp only [mul_zero] at hk
    have : q ≤ 1 := Nat.sub_eq_zero_iff_le.mp hk
    exact (not_le_of_gt hq.one_lt) this
  refine ⟨k, hkpos, ?_⟩
  calc
    q = (q - 1) + 1 := (Nat.sub_add_cancel hq.one_le).symm
    _ = p * k + 1 := by rw [hk]
    _ = k * p + 1 := by rw [mul_comm]

/-- A squared prime divisor of an integer supplies that prime to its totient.-/
theorem prime_dvd_totient_of_sq_dvd {q N : ℕ} (hq : q.Prime) (hqsq : q ^ 2 ∣ N) :
    q ∣ N.totient := by
  have hlocal : q ∣ (q ^ 2).totient := by
    rw [Nat.totient_prime_pow hq (by norm_num : 0 < (2 : ℕ))]
    simp
  exact hlocal.trans (Nat.totient_dvd_of_dvd hqsq)

/-- A prime divisor absent from the totient occurs to exponent exactly one in the integer.-/
theorem exists_cofactor_of_prime_dvd_not_dvd_totient {q N : ℕ} (hq : q.Prime)
    (hqdvd : q ∣ N) (hqtot : ¬q ∣ N.totient) :
    ∃ m : ℕ, N = m * q ∧ ¬q ∣ m := by
  refine ⟨N / q, (Nat.div_mul_cancel hqdvd).symm, ?_⟩
  intro hqcofactor
  apply hqtot
  apply prime_dvd_totient_of_sq_dvd hq
  have hsq : q * q ∣ (N / q) * q := Nat.mul_dvd_mul hqcofactor (dvd_refl q)
  rw [Nat.div_mul_cancel hqdvd] at hsq
  simpa only [pow_two] using hsq

/-- Removing a prime that occurs to exponent one exposes the corresponding Euler factor.-/
theorem totient_eq_cofactor_mul_pred {N m q : ℕ} (hq : q.Prime) (hN : N = m * q)
    (hqcofactor : ¬q ∣ m) : N.totient = m.totient * (q - 1) := by
  have hcoprime : m.Coprime q := (hq.coprime_iff_not_dvd.mpr hqcofactor).symm
  rw [hN, Nat.totient_mul hcoprime, Nat.totient_prime hq]

/-- Paper Lemma 3.1 (provider lemma).-/
theorem exists_prime_provider_of_dvd_totient {N p : ℕ} (hN : 1 ≤ N) (hp : p.Prime)
    (hptot : p ∣ N.totient) (hp_sq : ¬p ^ 2 ∣ N) :
    ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ p ∣ q - 1 := by
  have hN0 : N ≠ 0 := (Nat.zero_lt_of_lt hN).ne'
  rw [Nat.totient_eq_prod_factorization hN0] at hptot
  change p ∣ ∏ q ∈ N.factorization.support,
    q ^ (N.factorization q - 1) * (q - 1) at hptot
  obtain ⟨q, hqN, hpq⟩ :=
    exists_mem_dvd_finset_prod_of_prime hp N.factorization.support
      (fun q ↦ q ^ (N.factorization q - 1) * (q - 1)) hptot
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqN
  have hqdvd : q ∣ N := Nat.dvd_of_mem_primeFactors hqN
  rcases hp.dvd_mul.mp hpq with hp_pow | hp_pred
  · have hpdq : p ∣ q := hp.dvd_of_dvd_pow hp_pow
    have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpdq
    subst q
    have hpred_pos : 0 < N.factorization p - 1 := by
      by_contra hnot
      have hzero : N.factorization p - 1 = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero, pow_zero] at hp_pow
      exact hp.not_dvd_one hp_pow
    have htwo : 2 ≤ N.factorization p := Nat.sub_pos_iff_lt.mp hpred_pos
    exact False.elim (hp_sq ((hp.pow_dvd_iff_le_factorization hN0).2 htwo))
  · exact ⟨q, hq, hqdvd, hp_pred⟩

/-- The arithmetic data and conclusions of the paper's large-prime skeleton (Lemma 3.2).-/
structure LargePrimeSkeleton (h n p : ℕ) where
  /-- Provider prime dividing `n`.-/
  q1 : ℕ
  /-- Provider prime dividing `n + h`.-/
  q2 : ℕ
  /-- Multiplier satisfying `q1 = k1 * p + 1`.-/
  k1 : ℕ
  /-- Multiplier satisfying `q2 = k2 * p + 1`.-/
  k2 : ℕ
  /-- Cofactor in the decomposition of `n`.-/
  m1 : ℕ
  /-- Cofactor in the decomposition of `n + h`.-/
  m2 : ℕ
  q1_prime : q1.Prime
  q2_prime : q2.Prime
  k1_pos : 0 < k1
  k2_pos : 0 < k2
  q1_eq : q1 = k1 * p + 1
  q2_eq : q2 = k2 * p + 1
  q1_dvd : q1 ∣ n
  q2_dvd : q2 ∣ n + h
  n_eq : n = m1 * q1
  shifted_eq : n + h = m2 * q2
  q1_not_dvd_m1 : ¬q1 ∣ m1
  q2_not_dvd_m2 : ¬q2 ∣ m2
  balance : k1 * m1.totient = k2 * m2.totient
  multipliers_smooth : IsSmooth p (k1 * k2)
  multipliers_lpf_le : largestPrimeFactor (k1 * k2) ≤ p
  providers_ne : q1 ≠ q2

/-- Core form of paper Lemma 3.2.-/
theorem exists_largePrimeSkeleton_of_maximal_prime {h n M p : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hp : p.Prime) (hphi1 : n.totient = M) (hphi2 : (n + h).totient = M) (hpM : p ∣ M)
    (hmax : ∀ {q : ℕ}, q.Prime → q ∣ M → q ≤ p) (hph : h < p)
    (hpsq : ¬p ^ 2 ∣ n * (n + h)) : Nonempty (LargePrimeSkeleton h n p) := by
  have hnshift : 1 ≤ n + h := by omega
  have hp_phi1 : p ∣ n.totient := by rw [hphi1]; exact hpM
  have hp_phi2 : p ∣ (n + h).totient := by rw [hphi2]; exact hpM
  have hp_sq1 : ¬p ^ 2 ∣ n := by
    intro hdvd
    exact hpsq (dvd_mul_of_dvd_left hdvd (n + h))
  have hp_sq2 : ¬p ^ 2 ∣ n + h := by
    intro hdvd
    exact hpsq (dvd_mul_of_dvd_right hdvd n)
  obtain ⟨q1, hq1, hq1n, hpq1⟩ :=
    exists_prime_provider_of_dvd_totient hn hp hp_phi1 hp_sq1
  obtain ⟨q2, hq2, hq2n, hpq2⟩ :=
    exists_prime_provider_of_dvd_totient hnshift hp hp_phi2 hp_sq2
  have hp_lt_q1 : p < q1 := prime_lt_of_dvd_pred hp hq1 hpq1
  have hp_lt_q2 : p < q2 := prime_lt_of_dvd_pred hp hq2 hpq2
  have hq1_ne_q2 : q1 ≠ q2 := by
    intro heq
    have hq1shift : q1 ∣ n + h := by simpa [heq] using hq2n
    have hq1h : q1 ∣ h := by
      have hsub : q1 ∣ (n + h) - n := Nat.dvd_sub hq1shift hq1n
      simpa using hsub
    have hq1le : q1 ≤ h := Nat.le_of_dvd (by omega) hq1h
    omega
  have hq1M : ¬q1 ∣ M := by
    intro hdvd
    exact (not_le_of_gt hp_lt_q1) (hmax hq1 hdvd)
  have hq2M : ¬q2 ∣ M := by
    intro hdvd
    exact (not_le_of_gt hp_lt_q2) (hmax hq2 hdvd)
  have hq1phi : ¬q1 ∣ n.totient := by
    intro hdvd
    exact hq1M (hphi1 ▸ hdvd)
  have hq2phi : ¬q2 ∣ (n + h).totient := by
    intro hdvd
    exact hq2M (hphi2 ▸ hdvd)
  obtain ⟨m1, hn_eq, hq1m1⟩ :=
    exists_cofactor_of_prime_dvd_not_dvd_totient hq1 hq1n hq1phi
  obtain ⟨m2, hnshift_eq, hq2m2⟩ :=
    exists_cofactor_of_prime_dvd_not_dvd_totient hq2 hq2n hq2phi
  obtain ⟨k1, hk1pos, hq1_eq⟩ := exists_pos_mul_add_one_eq_of_dvd_pred hp hq1 hpq1
  obtain ⟨k2, hk2pos, hq2_eq⟩ := exists_pos_mul_add_one_eq_of_dvd_pred hp hq2 hpq2
  have htot1 : M = m1.totient * (k1 * p) := by
    calc
      M = n.totient := hphi1.symm
      _ = m1.totient * (q1 - 1) := totient_eq_cofactor_mul_pred hq1 hn_eq hq1m1
      _ = m1.totient * (k1 * p) := by rw [hq1_eq]; simp
  have htot2 : M = m2.totient * (k2 * p) := by
    calc
      M = (n + h).totient := hphi2.symm
      _ = m2.totient * (q2 - 1) := totient_eq_cofactor_mul_pred hq2 hnshift_eq hq2m2
      _ = m2.totient * (k2 * p) := by rw [hq2_eq]; simp
  have hbalance : k1 * m1.totient = k2 * m2.totient := by
    apply (mul_right_inj' hp.ne_zero).mp
    calc
      p * (k1 * m1.totient) = m1.totient * (k1 * p) := by ac_rfl
      _ = M := htot1.symm
      _ = m2.totient * (k2 * p) := htot2
      _ = p * (k2 * m2.totient) := by ac_rfl
  have hsmooth : IsSmooth p (k1 * k2) := by
    refine ⟨mul_ne_zero hk1pos.ne' hk2pos.ne', ?_⟩
    intro r hrmem
    have hr : r.Prime := Nat.prime_of_mem_primeFactors hrmem
    have hrdvd : r ∣ k1 * k2 := Nat.dvd_of_mem_primeFactors hrmem
    rcases hr.dvd_mul.mp hrdvd with hrk1 | hrk2
    · apply hmax hr
      rw [htot1]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hrk1 p) m1.totient
    · apply hmax hr
      rw [htot2]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hrk2 p) m2.totient
  exact ⟨{
    q1 := q1
    q2 := q2
    k1 := k1
    k2 := k2
    m1 := m1
    m2 := m2
    q1_prime := hq1
    q2_prime := hq2
    k1_pos := hk1pos
    k2_pos := hk2pos
    q1_eq := hq1_eq
    q2_eq := hq2_eq
    q1_dvd := hq1n
    q2_dvd := hq2n
    n_eq := hn_eq
    shifted_eq := hnshift_eq
    q1_not_dvd_m1 := hq1m1
    q2_not_dvd_m2 := hq2m2
    balance := hbalance
    multipliers_smooth := hsmooth
    multipliers_lpf_le := largestPrimeFactor_le_of_isSmooth hp.one_le hsmooth
    providers_ne := hq1_ne_q2
  }⟩

/-- Paper Lemma 3.2 (large-prime skeleton), with the inessential ambient bound `n ≤ x` omitted.-/
theorem exists_largePrimeSkeleton {h n M p : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hphi1 : n.totient = M) (hphi2 : (n + h).totient = M)
    (hpdef : p = largestPrimeFactor M) (hph : h < p)
    (hpsq : ¬p ^ 2 ∣ n * (n + h)) : Nonempty (LargePrimeSkeleton h n p) := by
  have hpgt1 : 1 < p := lt_of_le_of_lt hh hph
  have hlarge : 1 < largestPrimeFactor M := by simpa [hpdef] using hpgt1
  have hp : p.Prime := by
    rw [hpdef]
    exact largestPrimeFactor_prime hlarge
  have hpM : p ∣ M := by
    rw [hpdef]
    exact largestPrimeFactor_dvd hlarge
  have hMpos : 0 < M := by
    rw [← hphi1]
    exact Nat.totient_pos.mpr (Nat.zero_lt_of_lt hn)
  have hmax : ∀ {q : ℕ}, q.Prime → q ∣ M → q ≤ p := by
    intro q hq hqM
    rw [hpdef]
    exact prime_le_largestPrimeFactor hq hMpos.ne' hqM
  exact exists_largePrimeSkeleton_of_maximal_prime hn hh hp hphi1 hphi2 hpM hmax hph hpsq

end RankAmplification
