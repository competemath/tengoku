import Tengoku.Rankamplificationtotient.RankAmplification.SameSupportSUnitReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Prime-power shifts: the affine `S`-unit equation solved unconditionally Lemma 9.1 of Pollack--Pomerance--Treviño asserts that the set of same-support indices `J_h = {j ≥ 1 : primeSupport j = primeSupport (j + h)}` is finite for every `h > 0`. -/

namespace RankAmplification

noncomputable section

/-! ## Numbers supported on a single prime -/

/-- A positive natural number whose prime support is contained in `{p}` is a power of `p`.
@isnad1 id=iff.1h2v.s5.d0806fd2af23 from=translated src=- shape=5eaa96fb vocab=4040ccda
-/
theorem isPrimeSupportUnit_singleton_iff {p n : ℕ} (hp : p.Prime) :
    IsPrimeSupportUnit {p} n ↔ ∃ i : ℕ, n = p ^ i := by
  constructor
  · rintro ⟨hpos, hsub⟩
    refine ⟨n.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_⟩
    intro d hd hdn
    exact Finset.mem_singleton.mp (hsub (Nat.mem_primeFactors.mpr ⟨hd, hdn, hpos.ne'⟩))
  · rintro ⟨i, rfl⟩
    refine ⟨pow_pos hp.pos i, ?_⟩
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ p ^ i := Nat.dvd_of_mem_primeFactors hq
    exact Finset.mem_singleton.mpr
      ((Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow hqd))

/-- The prime support of a positive prime power `p ^ a` is `{p}`.
@isnad1 id=eq.2h2v.s5.63b20ba7f4e6 from=translated src=- shape=f9b1f770 vocab=11af024a
-/
theorem primeSupport_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    primeSupport (p ^ a) = {p} :=
  Nat.primeFactors_prime_pow ha.ne' hp

/-! ## The prime-power affine equation -/

/-- For `d ≥ 1` the number `p ^ d + 1` is `≡ 1 (mod p)` and exceeds `1`, hence is never a power of the prime `p`.
@isnad1 id=ne.2h3v.s5.dcd9bde7e65a from=translated src=- shape=de050987 vocab=65e9c7a8
-/
theorem prime_pow_add_one_ne_prime_pow {p d e : ℕ} (hp : p.Prime) (hd : 0 < d) :
    p ^ d + 1 ≠ p ^ e := by
  intro heq
  have hp2 := hp.two_le
  have hpd : p ∣ p ^ d := dvd_pow_self p hd.ne'
  have hple : 1 ≤ p ^ d := Nat.one_le_pow _ _ hp.pos
  have he : e ≠ 0 := by
    intro h
    rw [h, pow_zero] at heq
    have hple2 : p ≤ p ^ d := Nat.le_self_pow hd.ne' p
    omega
  have hpe : p ∣ p ^ d + 1 := by
    rw [heq]
    exact dvd_pow_self p he
  have hone : p ∣ 1 := by
    have hsub := Nat.dvd_sub hpe hpd
    simpa using hsub
  have := Nat.le_of_dvd Nat.one_pos hone
  omega

/-- The complete solution of `p ^ i + p ^ a = p ^ j` for a prime `p` and `a ≥ 1`: it forces `p = 2`, `i = a` and `j = a + 1`.-/
theorem eq_of_prime_pow_add_prime_pow_eq_prime_pow {p a i j : ℕ} (hp : p.Prime) (ha : 0 < a)
    (heq : p ^ i + p ^ a = p ^ j) : p = 2 ∧ i = a ∧ j = a + 1 := by
  have hppos : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  rcases lt_trichotomy i a with hlt | hia | hgt
  · exfalso
    have hdvd : p ^ i ∣ p ^ j := by
      rw [← heq]
      exact dvd_add dvd_rfl (pow_dvd_pow p hlt.le)
    have _hij : i ≤ j := (Nat.pow_dvd_pow_iff_le_right hp1).mp hdvd
    obtain ⟨d, rfl⟩ : ∃ d, a = i + d := ⟨a - i, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e, j = i + e := ⟨j - i, by omega⟩
    simp only [pow_add] at heq
    have h2 : p ^ i * (p ^ d + 1) = p ^ i * p ^ e := by
      calc p ^ i * (p ^ d + 1) = p ^ i + p ^ i * p ^ d := by ring
        _ = p ^ i * p ^ e := heq
    exact prime_pow_add_one_ne_prime_pow hp (by omega)
      (Nat.eq_of_mul_eq_mul_left (pow_pos hppos i) h2)
  · rw [hia] at heq
    have hdvd : p ^ a ∣ p ^ j := by
      rw [← heq]
      exact dvd_add dvd_rfl dvd_rfl
    have _haj : a ≤ j := (Nat.pow_dvd_pow_iff_le_right hp1).mp hdvd
    obtain ⟨e, rfl⟩ : ∃ e, j = a + e := ⟨j - a, by omega⟩
    rw [pow_add] at heq
    have h2 : p ^ a * 2 = p ^ a * p ^ e := by
      calc p ^ a * 2 = p ^ a + p ^ a := by ring
        _ = p ^ a * p ^ e := heq
    have h3 : (2 : ℕ) = p ^ e := Nat.eq_of_mul_eq_mul_left (pow_pos hppos a) h2
    have he0 : e ≠ 0 := by
      intro h
      rw [h, pow_zero] at h3
      exact absurd h3 (by norm_num)
    have hpdvd : p ∣ 2 := by
      rw [h3]
      exact dvd_pow_self p he0
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd
    subst hp2
    have he1 : e = 1 :=
      Nat.pow_right_injective (le_refl 2) (h3.symm.trans (pow_one 2).symm)
    exact ⟨rfl, hia, by omega⟩
  · exfalso
    have hdvd : p ^ a ∣ p ^ j := by
      rw [← heq]
      exact dvd_add (pow_dvd_pow p hgt.le) dvd_rfl
    have _haj : a ≤ j := (Nat.pow_dvd_pow_iff_le_right hp1).mp hdvd
    obtain ⟨d, rfl⟩ : ∃ d, i = a + d := ⟨i - a, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e, j = a + e := ⟨j - a, by omega⟩
    simp only [pow_add] at heq
    have h2 : p ^ a * (p ^ d + 1) = p ^ a * p ^ e := by
      calc p ^ a * (p ^ d + 1) = p ^ a * p ^ d + p ^ a := by ring
        _ = p ^ a * p ^ e := heq
    exact prime_pow_add_one_ne_prime_pow hp (by omega)
      (Nat.eq_of_mul_eq_mul_left (pow_pos hppos a) h2)

/-! ## Exact affine carriers for prime-power shifts -/

/-- For the shift `2 ^ a` the affine `S`-unit equation has exactly one positive solution.
@isnad1 id=issunita.1h1v.s6.7734c02afdec from=translated src=- shape=367bccfe vocab=04e961a7
-/
theorem isSUnitAffineCarrier_prime_pow_two {a : ℕ} (ha : 0 < a) :
    IsSUnitAffineCarrier (primeSupport (2 ^ a)) (2 ^ a) {(2 ^ a, 2 ^ (a + 1))} := by
  have hsupp : primeSupport (2 ^ a) = {2} := primeSupport_prime_pow Nat.prime_two ha
  intro u v
  rw [hsupp]
  constructor
  · intro hmem
    rw [Finset.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨hu, hv⟩ := hmem
    refine ⟨(isPrimeSupportUnit_singleton_iff Nat.prime_two).mpr ⟨a, hu⟩,
      (isPrimeSupportUnit_singleton_iff Nat.prime_two).mpr ⟨a + 1, hv⟩, ?_⟩
    rw [hu, hv, pow_succ, Nat.mul_two]
  · rintro ⟨hu, hv, huv⟩
    obtain ⟨i, rfl⟩ := (isPrimeSupportUnit_singleton_iff Nat.prime_two).mp hu
    obtain ⟨j, rfl⟩ := (isPrimeSupportUnit_singleton_iff Nat.prime_two).mp hv
    obtain ⟨-, hia, hja⟩ := eq_of_prime_pow_add_prime_pow_eq_prime_pow Nat.prime_two ha huv
    rw [Finset.mem_singleton, Prod.mk.injEq]
    exact ⟨by rw [hia], by rw [hja]⟩

/-- For the shift `p ^ a` with `p` an odd prime the affine `S`-unit equation has no positive solution at all.
@isnad1 id=issunita.3h2v.s6.40ca34b41212 from=translated src=- shape=e9648b91 vocab=f3d66687
-/
theorem isSUnitAffineCarrier_prime_pow_odd {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) :
    IsSUnitAffineCarrier (primeSupport (p ^ a)) (p ^ a) ∅ := by
  have hsupp : primeSupport (p ^ a) = {p} := primeSupport_prime_pow hp ha
  intro u v
  rw [hsupp]
  simp only [Finset.notMem_empty, false_iff]
  rintro ⟨hu, hv, huv⟩
  obtain ⟨i, rfl⟩ := (isPrimeSupportUnit_singleton_iff hp).mp hu
  obtain ⟨j, rfl⟩ := (isPrimeSupportUnit_singleton_iff hp).mp hv
  exact hp2 (eq_of_prime_pow_add_prime_pow_eq_prime_pow hp ha huv).1

/-- A prime-power shift has an exact affine carrier with at most one element.
@isnad1 id=ex.2h2v.s6.4e7665757df4 from=translated src=- shape=05a3dda2 vocab=c1fec46d
-/
theorem exists_isSUnitAffineCarrier_prime_pow_card_le_one {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    ∃ U : Finset (ℕ × ℕ), IsSUnitAffineCarrier (primeSupport (p ^ a)) (p ^ a) U ∧ U.card ≤ 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    exact ⟨{(2 ^ a, 2 ^ (a + 1))}, isSUnitAffineCarrier_prime_pow_two ha, by simp⟩
  · exact ⟨∅, isSUnitAffineCarrier_prime_pow_odd hp hp2 ha, by simp⟩

/-! ## Unconditional terminal endpoints for prime-power shifts -/

/-- The qualitative Evertse endpoint holds unconditionally for prime-power shifts.
@isnad1 id=terminal.2h2v.s5.44098dc980f1 from=translated src=- shape=58428754 vocab=05384dfa
-/
theorem terminalEvertseSUnitFiniteness_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    TerminalEvertseSUnitFiniteness (p ^ a) := by
  obtain ⟨U, hU, -⟩ := exists_isSUnitAffineCarrier_prime_pow_card_le_one hp ha
  exact ⟨U, hU⟩

/-- The quantitative Pollack--Pomerance--Treviño endpoint holds unconditionally for prime-power shifts: the same-support carrier has at most one element, far below the stated bound.
@isnad1 id=terminal.2h2v.s5.40054c158b89 from=translated src=- shape=58428754 vocab=9c58e909
-/
theorem terminalPPTSameSupportBound_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    TerminalPPTSameSupportBound (p ^ a) := by
  obtain ⟨U, hU, hcard⟩ := exists_isSUnitAffineCarrier_prime_pow_card_le_one hp ha
  refine ⟨sameSupportCarrierFromSUnit (p ^ a) U,
    isSameSupportCarrier_sameSupportCarrierFromSUnit (pow_pos hp.pos a) hU, ?_⟩
  have h1 : (sameSupportCarrierFromSUnit (p ^ a) U).card ≤ 1 :=
    le_trans (card_sameSupportCarrierFromSUnit_le _ _) hcard
  have h2 : 1 ≤ pptSameSupportBound (p ^ a) := by
    unfold pptSameSupportBound
    refine Nat.one_le_iff_ne_zero.mpr ?_
    positivity
  exact le_trans h1 h2

/-! ## The exact set of same-support indices for a power of two -/

/-- For `h = 2 ^ a` with `a ≥ 1` the same-support indices are exactly `{2 ^ a}`.
@isnad1 id=iff.1h2v.s5.a5e0116db0f0 from=translated src=- shape=2e696602 vocab=09136262
-/
theorem sameSupportIndices_two_pow {a j : ℕ} (ha : 0 < a) :
    IsSameSupportIndex (2 ^ a) j ↔ j = 2 ^ a := by
  constructor
  · intro hsame
    have hpos : 0 < (2 : ℕ) ^ a := pow_pos (by norm_num) a
    have hsol := sameSupport_isSUnitAffineSolution hpos hsame
    have hmem := (isSUnitAffineCarrier_prime_pow_two ha j (j + 2 ^ a)).mpr hsol
    rw [Finset.mem_singleton, Prod.mk.injEq] at hmem
    exact hmem.1
  · rintro rfl
    refine ⟨Nat.one_le_pow a 2 (by norm_num), ?_⟩
    have hsum : (2 : ℕ) ^ a + 2 ^ a = 2 ^ (a + 1) := by
      rw [pow_succ, Nat.mul_two]
    rw [primeSupport_prime_pow Nat.prime_two ha, hsum,
      primeSupport_prime_pow Nat.prime_two (Nat.succ_pos a)]

end

end RankAmplification
