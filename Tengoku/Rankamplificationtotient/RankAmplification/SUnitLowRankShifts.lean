import Tengoku.Rankamplificationtotient.RankAmplification.SUnitPrimePower
import Tengoku.Rankamplificationtotient.RankAmplification.SUnitTerminal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Unconditional same-support results for low-rank shifts Lemma 9.1 of the paper asserts that the same-support index set `J_h = { j ≥ 1 : primeSupport j = primeSupport (j + h) }` is finite. -/

namespace RankAmplification

open Finset

noncomputable section

/-! ## Shifts with at most one prime factor -/

/-- A positive number whose prime support is contained in `{p}` is a power of `p`.-/
theorem eq_prime_pow_of_primeSupport_subset_singleton {n p : ℕ} (hn : 0 < n)
    (hsub : primeSupport n ⊆ {p}) : ∃ k : ℕ, n = p ^ k := by
  refine ⟨n.primeFactorsList.length, ?_⟩
  apply Nat.eq_prime_pow_of_unique_prime_dvd hn.ne'
  intro d hd hdvd
  have hmem : d ∈ primeSupport n := Nat.mem_primeFactors.mpr ⟨hd, hdvd, hn.ne'⟩
  simpa using hsub hmem

/-- A shift with a one-element prime support is a positive power of that prime.
@isnad1 id=ex.2h2v.s5.a112e444b6fb from=translated src=- shape=79267af9 vocab=9b0501ce
-/
theorem exists_pos_pow_of_primeSupport_eq_singleton {h p : ℕ} (hh : 0 < h)
    (hsupp : primeSupport h = {p}) : ∃ a : ℕ, 0 < a ∧ h = p ^ a := by
  obtain ⟨k, hk⟩ := eq_prime_pow_of_primeSupport_subset_singleton hh (by rw [hsupp])
  refine ⟨k, ?_, hk⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exfalso
    have hone : h = 1 := by simpa [hk0] using hk
    have : primeSupport h = ∅ := by simp [hone, primeSupport]
    rw [hsupp] at this
    exact (Finset.singleton_ne_empty p) this
  · exact hk0

/-- Every shift whose prime support has at most one element admits an exact finite carrier for the affine `S`-unit equation.
@isnad1 id=terminal.1h1v.s4.ae6763b0d31f from=translated src=- shape=923eeeab vocab=eda801ce
-/
theorem terminalEvertseSUnitFiniteness_of_card_primeSupport_le_one
    {h : ℕ} (hcard : (primeSupport h).card ≤ 1) :
    TerminalEvertseSUnitFiniteness h := by
  rcases Nat.eq_zero_or_pos h with hh | hh
  · subst hh
    exact SUnitTerminal.terminalEvertseSUnitFiniteness_zero
  · rcases Nat.lt_or_ge (primeSupport h).card 1 with hzero | hone
    · -- empty support and `h > 0` force `h = 1`, which is odd
      have hempty : primeSupport h = ∅ := Finset.card_eq_zero.mp (by omega)
      have hone : h = 1 := by
        by_contra hne
        have h2 : 2 ≤ h := by omega
        obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (show h ≠ 1 from hne)
        have hmem : p ∈ primeSupport h :=
          Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, hh.ne'⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty p)
      subst hone
      exact terminalEvertseSUnitFiniteness_of_odd ⟨0, by norm_num⟩
    · have hcardOne : (primeSupport h).card = 1 := by omega
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcardOne
      have hpmem : p ∈ primeSupport h := by
        rw [hp]; exact Finset.mem_singleton_self p
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      obtain ⟨a, ha, hpow⟩ := exists_pos_pow_of_primeSupport_eq_singleton hh hp
      rw [hpow]
      exact terminalEvertseSUnitFiniteness_prime_pow hpPrime ha

/-- The quantitative Pollack--Pomerance--Treviño bound holds unconditionally for every shift with at most one prime factor.
@isnad1 id=terminal.2h1v.s4.ee156ad38c7c from=translated src=- shape=66d847ae vocab=66b3778c
-/
theorem terminalPPTSameSupportBound_of_card_primeSupport_le_one
    {h : ℕ} (hh : 0 < h) (hcard : (primeSupport h).card ≤ 1) :
    TerminalPPTSameSupportBound h := by
  rcases Nat.lt_or_ge (primeSupport h).card 1 with hzero | hone
  · have hempty : primeSupport h = ∅ := Finset.card_eq_zero.mp (by omega)
    have hone : h = 1 := by
      by_contra hne
      obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (show h ≠ 1 from hne)
      have hmem : p ∈ primeSupport h :=
        Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, hh.ne'⟩
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty p)
    subst hone
    exact terminalPPTSameSupportBound_of_odd ⟨0, by norm_num⟩
  · have hcardOne : (primeSupport h).card = 1 := by omega
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcardOne
    have hpmem : p ∈ primeSupport h := by
      rw [hp]; exact Finset.mem_singleton_self p
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    obtain ⟨a, ha, hpow⟩ := exists_pos_pow_of_primeSupport_eq_singleton hh hp
    rw [hpow]
    exact terminalPPTSameSupportBound_prime_pow hpPrime ha

/-! ## The rank-one part of `J_h` for an arbitrary shift -/

/-- If `p^α + h = p^γ` with `α < γ`, then `α` is exactly the `p`-adic valuation of `h`.
@isnad1 id=eq.3h4v.s6.629c1039eadf from=translated src=- shape=fb5f85f3 vocab=728de956
-/
theorem factorization_eq_of_prime_pow_shift {h p α γ : ℕ} (hp : p.Prime)
    (hlt : α < γ) (heq : p ^ α + h = p ^ γ) : h.factorization p = α := by
  have hppos : 0 < p := hp.pos
  have hpow : p ^ γ = p ^ α * p ^ (γ - α) := by
    rw [← pow_add]; congr 1; omega
  obtain ⟨m, hm⟩ : ∃ m, p ^ (γ - α) = m + 1 :=
    ⟨p ^ (γ - α) - 1, by
      have : 1 ≤ p ^ (γ - α) := Nat.one_le_pow _ _ hppos
      omega⟩
  have hexpand : p ^ α * (m + 1) = p ^ α * m + p ^ α := by ring
  have hfac : h = p ^ α * m := by
    rw [hm] at hpow
    omega
  have hmpos : 0 < m := by
    have h2 : 2 ≤ p ^ (γ - α) := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (γ - α) := Nat.pow_le_pow_right hppos (by omega)
    omega
  have hnd : ¬ p ∣ m := by
    intro hdvd
    have hpdvd : p ∣ p ^ (γ - α) := dvd_pow_self p (by omega)
    rw [hm] at hpdvd
    have hone : p ∣ 1 := by
      have := Nat.dvd_sub hpdvd hdvd
      simpa using this
    exact Nat.Prime.one_lt hp |>.ne'
      (Nat.le_antisymm (Nat.le_of_dvd one_pos hone) hp.one_lt.le)
  rw [hfac, Nat.factorization_mul (pow_ne_zero _ hppos.ne') hmpos.ne']
  simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]

/-- A same-support index whose own prime support is the single prime `p` is uniquely determined: it must equal `p ^ v_p(h)`.
@isnad1 id=eq.4h3v.s6.868adc8354c2 from=translated src=- shape=a36e5c1c vocab=6ffa4b68
-/
theorem sameSupportIndex_singleton_eq {h p j : ℕ} (hp : p.Prime) (hh : 0 < h)
    (hj : IsSameSupportIndex h j) (hjp : primeSupport j = {p}) :
    j = p ^ h.factorization p := by
  have hjpos : 0 < j := hj.1
  obtain ⟨α, hα⟩ := eq_prime_pow_of_primeSupport_subset_singleton hjpos (by rw [hjp])
  obtain ⟨γ, hγ⟩ := eq_prime_pow_of_primeSupport_subset_singleton
    (by omega : 0 < j + h) (by rw [← hj.2, hjp])
  have heq : p ^ α + h = p ^ γ := by rw [← hα, ← hγ]
  have hlt : α < γ := by
    have hmono : p ^ α < p ^ γ := by omega
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hmono
  rw [hα, factorization_eq_of_prime_pow_shift hp hlt heq]

/-- At most one same-support index has any given singleton prime support.
@isnad1 id=eq.6h4v.s5.f336603ef008 from=translated src=- shape=3a57da87 vocab=2f54cc8b
-/
theorem sameSupportIndex_singleton_unique {h p j k : ℕ} (hp : p.Prime) (hh : 0 < h)
    (hj : IsSameSupportIndex h j) (hjp : primeSupport j = {p})
    (hk : IsSameSupportIndex h k) (hkp : primeSupport k = {p}) :
    j = k :=
  (sameSupportIndex_singleton_eq hp hh hj hjp).trans
    (sameSupportIndex_singleton_eq hp hh hk hkp).symm

/-- The prime in a singleton support divides the shift.
@isnad1 id=mem.3h3v.s5.5d32a007a8eb from=translated src=- shape=122f2d36 vocab=1ae4ffee
-/
theorem singleton_support_prime_mem_primeSupport {h p j : ℕ} (hh : 0 < h)
    (hj : IsSameSupportIndex h j) (hjp : primeSupport j = {p}) :
    p ∈ primeSupport h := by
  have hmem : p ∈ primeSupport j := by rw [hjp]; simp
  exact primeSupport_subset_shift_of_sameSupport hh hj hmem

/-- Unconditional finite carrier for the rank-one part of `J_h`, valid for every positive shift.-/
def rankOneSameSupportCarrier (h : ℕ) : Finset ℕ := by
  classical
  exact ((primeSupport h).image fun p ↦ p ^ h.factorization p).filter
    (IsSameSupportIndex h)

/--
@isnad1 id=mem.4h3v.s5.f92f804cb907 from=translated src=- shape=e9b3e70a vocab=a87a1066
-/
theorem mem_rankOneSameSupportCarrier_of {h j : ℕ} (hh : 0 < h)
    (hj : IsSameSupportIndex h j) {p : ℕ} (hp : p.Prime)
    (hjp : primeSupport j = {p}) :
    j ∈ rankOneSameSupportCarrier h := by
  classical
  rw [rankOneSameSupportCarrier, Finset.mem_filter]
  refine ⟨Finset.mem_image.mpr
    ⟨p, singleton_support_prime_mem_primeSupport hh hj hjp, ?_⟩, hj⟩
  exact (sameSupportIndex_singleton_eq hp hh hj hjp).symm

/--
@isnad1 id=issamesu.1h2v.s4.758418db614d from=translated src=- shape=30a1b31e vocab=2f56b05f
-/
theorem isSameSupportIndex_of_mem_rankOneSameSupportCarrier
    {h j : ℕ} (hj : j ∈ rankOneSameSupportCarrier h) :
    IsSameSupportIndex h j := by
  classical
  exact (Finset.mem_filter.mp hj).2

/-- The rank-one part of `J_h` has at most `ω(h)` elements, for every shift.
@isnad1 id=le.0h1v.s3.a17e32398225 from=translated src=- shape=93f360f3 vocab=6888f733
-/
theorem card_rankOneSameSupportCarrier_le (h : ℕ) :
    (rankOneSameSupportCarrier h).card ≤ (primeSupport h).card := by
  classical
  exact (Finset.card_filter_le _ _).trans Finset.card_image_le

end

end RankAmplification
