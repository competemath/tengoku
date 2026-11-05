module

public import Tengoku.KummerCriterion.KummerCriterion.HMinus.KplusPrimeArithmetic
public import Tengoku.KummerCriterion.KummerCriterion.ZetaFactorisation.NumberFieldEulerProduct
import Tengoku.KummerCriterion.KummerCriterion.ZetaFactorisation.EulerProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `K⁺` Euler product and residue bridge

Euler-product comparison between the zeta function of `K⁺` and even Dirichlet
`L`-products.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators Topology nonZeroDivisors

namespace KummerCriterion

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

abbrev NonzeroIdealNF (L : Type*) [Field L] [NumberField L] : Type _ := NonzeroIdeal L

abbrev idealNormMultiplicityNF (L : Type*) [Field L] [NumberField L] (n : ℕ) : ℕ :=
  idealNormMultiplicity L n

/--
@isnad1 id=eq.1h2v.s7.8ec3035236c0 from=translated src=- shape=81d21a34 vocab=4fb4f3f5
-/
lemma dedekindZeta_eq_tprod_primePowerSeriesNF
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' q : Nat.Primes,
        (∑' k : ℕ, (idealNormMultiplicityNF L ((q : ℕ) ^ k) : ℂ) *
          ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))) := by
  simpa [idealNormMultiplicityNF] using
    (dedekindZeta_eq_tprod_primePowerSeries (L := L) hs)

/--
@isnad1 id=eq.1h3v.s6.3acf422a1672 from=translated src=- shape=7c4cda8c vocab=f57e778f
-/
lemma idealNormMultiplicityNF_p_pow_eq_one_plus (hp_odd : p ≠ 2) (k : ℕ) :
    idealNormMultiplicityNF K⁺ (p ^ k) = 1 := by
  classical
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  have hcard : (primesOverFinsetPlus (K := K) p).card = 1 := by
    rw [primesOverFinsetPlus_card_eq_ncard (K := K) (ℓ := p)]
    exact ncard_primesOverPlus_at_p_eq_one (p := p) (K := K)
  obtain ⟨PPlus, hPPlus⟩ := Finset.card_eq_one.mp hcard
  have hPPlusmem : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K⁺) := by
    have hPPlus_fin : PPlus ∈ primesOverFinsetPlus (K := K) p := by
      rw [hPPlus]
      exact Finset.mem_singleton_self PPlus
    exact (mem_primesOverFinsetPlus_iff (K := K) (ℓ := p)).1 hPPlus_fin
  have hPPlus_ne : PPlus ≠ ⊥ := by
    intro hPPlus_bot
    have hunder := hPPlusmem.2
    rw [Ideal.liesOver_iff, Ideal.under_def, hPPlus_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 K⁺))
        (FaithfulSMul.algebraMap_injective ℤ (𝓞 K⁺))] at hunder
    have hne : (rationalPrimeIdeal p) ≠ ⊥ := by
      rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.out.ne_zero
    exact hne hunder
  have : PPlus.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hPPlus_ne hPPlusmem.1
  have : PPlus.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hPPlusmem.2
  have habsNormPPlus : Ideal.absNorm PPlus = p := by
    calc
      Ideal.absNorm PPlus = p ^ (1 : ℕ) := by
        rw [← primesOverPlus_inertiaDeg_eq_one_at_p (p := p) (K := K) PPlus hPPlusmem]
        exact (Ideal.pow_inertiaDeg p PPlus).symm
      _ = p := by simp
  have : Unique {I : NonzeroIdealNF K⁺ // Ideal.absNorm I.1 = p ^ k} :=
    { default := ⟨⟨PPlus ^ k, pow_ne_zero k hPPlus_ne⟩, by
          rw [map_pow, habsNormPPlus]⟩
      uniq := by
        rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
        let m : ℕ := Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I)
        obtain ⟨Q, hPQ, hIeq⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne PPlus
        have hQ_top : Q = ⊤ := by
          by_contra hQ_ne_top
          have hQ_ne : Q ≠ ⊥ := by
            intro hQ_bot
            apply hI_ne
            rw [hIeq, hQ_bot, Ideal.mul_bot]
          have hnf_ne : UniqueFactorizationMonoid.normalizedFactors Q ≠ 0 := by
            intro hnf
            apply hQ_ne_top
            rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne, hnf]
            simp
          obtain ⟨R, hRmem⟩ := Multiset.exists_mem_of_ne_zero hnf_ne
          have hRfac := (Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
          have hRprime : R.IsPrime := hRfac.1
          have hQ_le_R : Q ≤ R := hRfac.2
          have hR_ne : R ≠ ⊥ := fun hR_bot =>
            hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          have : NeZero R := ⟨hR_ne⟩
          have hI_le_Q : I ≤ Q := by
            rw [hIeq]
            exact Ideal.mul_le_right
          have hR_dvd_I : Ideal.absNorm R ∣ p ^ k := by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have hunder_dvd : Ideal.absNorm (Ideal.under ℤ R) ∣ p ^ k :=
            dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
          have hunder_prime : (Ideal.absNorm (Ideal.under ℤ R)).Prime := Nat.absNorm_under_prime R
          have hunder_dvd_p : Ideal.absNorm (Ideal.under ℤ R) ∣ p :=
            hunder_prime.dvd_of_dvd_pow hunder_dvd
          have hunder_eq_p : Ideal.absNorm (Ideal.under ℤ R) = p :=
            (Nat.prime_dvd_prime_iff_eq hunder_prime hp.out).1 hunder_dvd_p
          have hunder_eq_span_p : Ideal.under ℤ R = Ideal.span {(p : ℤ)} := by
            rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]
            simp [hunder_eq_p]
          have hR_lies : R.LiesOver (Ideal.span {(p : ℤ)}) := by
            rw [Ideal.liesOver_iff, hunder_eq_span_p]
          have hRmem_p : R ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K⁺) := by
            refine ⟨hRprime, ?_⟩
            simpa [rationalPrimeIdeal] using hR_lies
          have hRmem_fin : R ∈ primesOverFinsetPlus (K := K) p :=
            (mem_primesOverFinsetPlus_iff (K := K) (ℓ := p)).2 hRmem_p
          have hR_eq_PPlus : R = PPlus := by
            rw [hPPlus] at hRmem_fin
            exact Finset.mem_singleton.mp hRmem_fin
          have hQ_le_PPlus : Q ≤ PPlus := by
            simpa [hR_eq_PPlus] using hQ_le_R
          have htop_le_PPlus : (⊤ : Ideal (𝓞 K⁺)) ≤ PPlus := by
            calc
              ⊤ = PPlus ⊔ Q := hPQ.symm
              _ ≤ PPlus := sup_le le_rfl hQ_le_PPlus
          exact hPPlusmem.1.ne_top (top_le_iff.mp htop_le_PPlus)
        have hI_pow : I = PPlus ^ m := by
          simpa [m, hQ_top] using hIeq
        have hm : m = k := by
          apply Nat.pow_right_injective hp.out.one_lt
          calc
            p ^ m = Ideal.absNorm I := by
              rw [hI_pow, map_pow, habsNormPPlus]
            _ = p ^ k := hI_norm
        refine Subtype.ext (Subtype.ext ?_)
        simpa [m, hm] using hI_pow }
  exact Nat.card_unique

/--
@isnad1 id=le.2h4v.s12.661a208bf356 from=translated src=- shape=890d473a vocab=a369126c
-/
lemma normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow
    {q : Nat.Primes} {I : Ideal (𝓞 K⁺)} (hI_ne : I ≠ ⊥)
    {k : ℕ} (hI_norm : Ideal.absNorm I = (q : ℕ) ^ k) :
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆
      primesOverFinsetPlus (K := K) (q : ℕ) := by
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  intro PPlus hPPlus
  have hPPlus_mem : PPlus ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.mem_toFinset.1 hPPlus
  have hPPlus_fac := (Ideal.mem_normalizedFactors_iff hI_ne).1 hPPlus_mem
  have hPPlus_prime : PPlus.IsPrime := hPPlus_fac.1
  have hI_le_PPlus : I ≤ PPlus := hPPlus_fac.2
  have hPPlus_ne : PPlus ≠ ⊥ := fun hPPlus_bot =>
    hI_ne (le_bot_iff.mp (hPPlus_bot ▸ hI_le_PPlus))
  have : NeZero PPlus := ⟨hPPlus_ne⟩
  have hPPlus_dvd : Ideal.absNorm PPlus ∣ (q : ℕ) ^ k := by
    rw [← hI_norm]
    exact Ideal.absNorm_dvd_absNorm_of_le hI_le_PPlus
  have hunder_dvd : Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q : ℕ) ^ k :=
    dvd_trans (Int.absNorm_under_dvd_absNorm PPlus) hPPlus_dvd
  have hunder_prime : (Ideal.absNorm (Ideal.under ℤ PPlus)).Prime := Nat.absNorm_under_prime PPlus
  have hunder_dvd_q : Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q : ℕ) :=
    hunder_prime.dvd_of_dvd_pow hunder_dvd
  have hunder_eq_q : Ideal.absNorm (Ideal.under ℤ PPlus) = (q : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime q.2).1 hunder_dvd_q
  have hunder_eq_span_q : Ideal.under ℤ PPlus = Ideal.span {((q : ℕ) : ℤ)} := by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ PPlus)]
    simp [hunder_eq_q]
  have hPPlus_lies : PPlus.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    rw [Ideal.liesOver_iff, hunder_eq_span_q]
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal (q : ℕ)) (𝓞 K⁺) := by
    refine ⟨hPPlus_prime, ?_⟩
    simpa [rationalPrimeIdeal] using hPPlus_lies
  exact (mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).2 hPPlus_over

/--
@isnad1 id=eq.3h4v.s11.d5866022b893 from=translated src=- shape=877629c8 vocab=d42facab
-/
lemma absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p)
    {PPlus : Ideal (𝓞 K⁺)}
    (hPPlus : PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)) :
    Ideal.absNorm PPlus = (q : ℕ) ^ localResidueDegreePlus (p := p) (q : ℕ) hq := by
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal (q : ℕ)) (𝓞 K⁺) :=
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).1 hPPlus
  have : PPlus.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hPPlus_over.2
  have : (rationalPrimeIdeal (q : ℕ)).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime (q : ℕ)
  have : PPlus.IsMaximal := Ideal.isMaximal_of_mem_primesOver hPPlus_over
  rw [← primesOver_inertiaDeg_eq_localResidueDegreePlus
    (p := p) (K := K) hp_odd hq PPlus hPPlus_over]
  exact (Ideal.pow_inertiaDeg (q : ℕ) PPlus).symm

/--
@isnad1 id=eq.4h5v.s12.fb972be1d24c from=translated src=- shape=2e07d0a2 vocab=24b70f71
-/
lemma normalizedFactors_card_mul_localResidueDegreePlus_of_absNorm_prime_pow
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p)
    {I : Ideal (𝓞 K⁺)} (hI_ne : I ≠ ⊥) {k : ℕ}
    (hI_norm : Ideal.absNorm I = (q : ℕ) ^ k) :
    localResidueDegreePlus (p := p) (q : ℕ) hq *
        (UniqueFactorizationMonoid.normalizedFactors I).card = k := by
  classical
  set d := localResidueDegreePlus (p := p) (q : ℕ) hq with hd
  set m := UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsubset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
    simpa [hm] using
      normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow (K := K) hI_ne hI_norm
  have hsum_count : ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus = m.card :=
    Multiset.sum_count_eq_card fun PPlus hPPlus => hsubset (Multiset.mem_toFinset.2 hPPlus)
  have hnorm_factors : Ideal.absNorm m.prod = (q : ℕ) ^ (d * m.card) := by
    rw [Finset.prod_multiset_count_of_subset m (primesOverFinsetPlus (K := K) (q : ℕ)) hsubset,
      map_prod]
    calc
      ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), Ideal.absNorm (PPlus ^ m.count PPlus)
          = ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ),
              ((q : ℕ) ^ d) ^ m.count PPlus := by
              apply Finset.prod_congr rfl
              intro PPlus hPPlus
              rw [map_pow]
              rw [absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
                (p := p) (K := K) hp_odd hq hPPlus, hd]
      _ = (q : ℕ) ^
          (d * ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus) := by
              rw [Finset.prod_pow_eq_pow_sum]
              simp [Nat.pow_mul]
      _ = (q : ℕ) ^ (d * m.card) := by rw [hsum_count]
  have hpow : (q : ℕ) ^ (d * m.card) = (q : ℕ) ^ k := by
    calc
      (q : ℕ) ^ (d * m.card) = Ideal.absNorm m.prod := hnorm_factors.symm
      _ = Ideal.absNorm I := by rw [hm, Ideal.prod_normalizedFactors_eq_self hI_ne]
      _ = (q : ℕ) ^ k := hI_norm
  exact Nat.pow_right_injective q.2.one_lt hpow

/--
@isnad1 id=eq.3h4v.s7.3680f509c64c from=translated src=- shape=cf6f02b8 vocab=64bf9b3a
-/
lemma idealNormMultiplicityNF_prime_pow_eq_zero_of_not_dvd_plus
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p)
    {k : ℕ} (hk : ¬ localResidueDegreePlus (p := p) (q : ℕ) hq ∣ k) :
    idealNormMultiplicityNF K⁺ ((q : ℕ) ^ k) = 0 := by
  unfold idealNormMultiplicityNF idealNormMultiplicity
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
  apply hk
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors I).card, ?_⟩
  simpa [mul_comm] using
    (normalizedFactors_card_mul_localResidueDegreePlus_of_absNorm_prime_pow
      (p := p) (K := K) hp_odd hq hI_ne hI_norm).symm

/--
@isnad1 id=eq.2h4v.s11.b9a6e74db50b from=translated src=- shape=31dfdcb7 vocab=41066a85
-/
lemma idealNormMultiplicityNF_prime_pow_mul_localResidueDegreePlus_eq_card_sym
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p) (n : ℕ) :
    idealNormMultiplicityNF K⁺
        ((q : ℕ) ^ (localResidueDegreePlus (p := p) (q : ℕ) hq * n)) =
      Fintype.card (Sym {PPlus : Ideal (𝓞 K⁺) //
        PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)} n) := by
  classical
  set d := localResidueDegreePlus (p := p) (q : ℕ) hq with hd
  let α : Type _ :=
    {PPlus : Ideal (𝓞 K⁺) // PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)}
  let β : Type _ := {I : NonzeroIdealNF K⁺ // Ideal.absNorm I.1 = (q : ℕ) ^ (d * n)}
  have hd_raw_pos : 0 < localResidueDegree (p := p) (q : ℕ) hq := by
    dsimp [localResidueDegree]
    exact orderOf_pos (unitOfPrimeNe (p := p) (q : ℕ) hq)
  have hd_pos : 0 < d := by
    rw [hd]
    by_cases hde : Even (localResidueDegree (p := p) (q : ℕ) hq)
    · rcases hde with ⟨k, hk⟩
      rw [localResidueDegreePlus_eq_half (p := p) hq ⟨k, hk⟩, hk]
      omega
    · rw [localResidueDegreePlus_eq_self (p := p) hq hde]
      exact hd_raw_pos
  have hpmap_val :
      ∀ {m : Multiset (Ideal (𝓞 K⁺))}
        (H : ∀ PPlus, PPlus ∈ m → PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)),
        Multiset.map Subtype.val
          (Multiset.pmap (fun PPlus hPPlus => (⟨PPlus, hPPlus⟩ : α)) m H) = m := by
    intro m H
    rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']
  let toSym : β → Sym α n := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ =>
    let m := UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ PPlus, PPlus ∈ m → PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ) := by
      intro PPlus hPPlus
      have hsubset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
        simpa [m] using
          normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow (K := K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    have hm_card : m.card = n := by
      have hmul : d * m.card = d * n := by
        simpa [m, hd] using
          normalizedFactors_card_mul_localResidueDegreePlus_of_absNorm_prime_pow
            (p := p) (K := K) hp_odd hq hI_ne hI_norm
      exact Nat.eq_of_mul_eq_mul_left hd_pos hmul
    ⟨Multiset.pmap (fun PPlus hPPlus => (⟨PPlus, hPPlus⟩ : α)) m H, by
      simp [hm_card]⟩
  let ofSym : Sym α n → β := fun s =>
    let m : Multiset (Ideal (𝓞 K⁺)) := s.1.map Subtype.val
    have hm_card : m.card = n := by
      simp [m]
    have hm_subset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
      intro PPlus hPPlus
      rcases Multiset.mem_toFinset.1 hPPlus with hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus, hQPlus, rfl⟩
      exact QPlus.2
    have hm_prime : ∀ PPlus ∈ m, Prime PPlus := by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus, hQPlus, rfl⟩
      have hQPlus_ne : (QPlus : Ideal (𝓞 K⁺)) ≠ ⊥ := by
        intro hQPlus_bot
        have hQPlus_norm :=
          absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
            (p := p) (K := K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot, ← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).1 QPlus.2).1
    have hm_prod_ne : m.prod ≠ ⊥ := Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm : Ideal.absNorm m.prod = (q : ℕ) ^ (d * n) := by
      have hsum_count :
          ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus = m.card :=
        Multiset.sum_count_eq_card fun PPlus hPPlus =>
          hm_subset (Multiset.mem_toFinset.2 hPPlus)
      rw [Finset.prod_multiset_count_of_subset m
        (primesOverFinsetPlus (K := K) (q : ℕ)) hm_subset, map_prod]
      calc
        ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), Ideal.absNorm (PPlus ^ m.count PPlus)
            = ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ),
                ((q : ℕ) ^ d) ^ m.count PPlus := by
                apply Finset.prod_congr rfl
                intro PPlus hPPlus
                rw [map_pow]
                rw [absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
                  (p := p) (K := K) hp_odd hq hPPlus, hd]
        _ = (q : ℕ) ^
            (d * ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus) := by
                rw [Finset.prod_pow_eq_pow_sum]
                simp [Nat.pow_mul]
        _ = (q : ℕ) ^ (d * m.card) := by rw [hsum_count]
        _ = (q : ℕ) ^ (d * n) := by rw [hm_card]
    ⟨⟨m.prod, hm_prod_ne⟩, hm_norm⟩
  have htoSym_map_val :
      ∀ b : β,
        (toSym b).1.map Subtype.val = UniqueFactorizationMonoid.normalizedFactors b.1.1 := by
    rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
    dsimp [toSym]
    let m := UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ PPlus, PPlus ∈ m → PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ) := by
      intro PPlus hPPlus
      have hsubset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
        simpa [m] using
          normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow (K := K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    change (Multiset.pmap (fun PPlus hPPlus => (⟨PPlus, hPPlus⟩ : α)) m H).map Subtype.val = m
    rw [hpmap_val H]
  have hofSym_nfactors :
      ∀ s : Sym α n,
        UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1 = s.1.map Subtype.val := by
    intro s
    dsimp [ofSym]
    let m : Multiset (Ideal (𝓞 K⁺)) := s.1.map Subtype.val
    have hm_prime : ∀ PPlus ∈ m, Prime PPlus := by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus, hQPlus, rfl⟩
      have hQPlus_ne : (QPlus : Ideal (𝓞 K⁺)) ≠ ⊥ := by
        intro hQPlus_bot
        have hQPlus_norm :=
          absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
            (p := p) (K := K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot, ← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).1 QPlus.2).1
    change UniqueFactorizationMonoid.normalizedFactors m.prod = m
    exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hm_prime
  have hleft : Function.LeftInverse ofSym toSym := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((toSym b).1.map Subtype.val).prod = b.1.1
    rw [htoSym_map_val, Ideal.prod_normalizedFactors_eq_self b.1.2]
  have hright : Function.RightInverse ofSym toSym := by
    intro s
    apply Subtype.ext
    apply Multiset.map_injective Subtype.val_injective
    simpa [hofSym_nfactors s] using htoSym_map_val (ofSym s)
  unfold idealNormMultiplicityNF idealNormMultiplicity
  simpa [β, α, hd, Nat.card_eq_fintype_card] using
    Nat.card_congr (⟨toSym, ofSym, hleft, hright⟩ : β ≃ Sym α n)

/--
@isnad1 id=eq.1h2v.s7.f0eae31d0d7b from=translated src=- shape=94b3b82a vocab=1257ecba
-/
lemma evenLProduct_eq_tprod_localFactors {s : ℂ} (hs : 1 < s.re) :
    evenLProduct p s =
      ∏' q : Nat.Primes,
        ∏ χ ∈ evenNontrivialCharacters (p := p),
          (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹ := by
  classical
  unfold evenLProduct
  rw [Finset.prod_congr rfl (fun χ _ => LFunction_eq_prime_tprod_of_localFactors p χ hs)]
  exact (Multipliable.tprod_finsetProd
    (s := evenNontrivialCharacters (p := p))
    (fun χ _ => (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable)).symm

/--
@isnad1 id=eq.1h2v.s5.8195b3572688 from=translated src=- shape=26d5fed5 vocab=cfe3baf8
-/
lemma evenLProduct_eq_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    evenLProduct p s =
      ∏' q : Nat.Primes, (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹ := by
  classical
  rw [evenLProduct_eq_tprod_localFactors (p := p) hs]
  refine tprod_congr fun q => ?_
  unfold evenCharLocalFactor
  rw [Finset.prod_inv_distrib]

/--
@isnad1 id=eq.0h2v.s4.20ba5c367ebd from=translated src=- shape=9fe17447 vocab=83034160
-/
lemma evenCharLocalFactor_at_p {s : ℂ} :
    evenCharLocalFactor (p := p) p s = 1 := by
  classical
  exact Finset.prod_eq_one fun χ _ => by
    rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, sub_zero]

/--
@isnad1 id=tendsto.0h1v.s6.367240d1e47c from=translated src=- shape=c446f754 vocab=ece4eb2b
-/
theorem tendsto_sub_one_mul_riemannZeta_mul_evenLProduct :
    Filter.Tendsto
      (fun s : ℝ ↦ (s - 1) * (riemannZeta (s : ℂ) * evenLProduct p (s : ℂ)))
      (𝓝[>] 1)
      (𝓝 (evenLProduct p (1 : ℂ))) := by
  classical
  have h_cont : Continuous (evenLProduct p) :=
    continuous_finsetProd _ fun χ hχ =>
      (DirichletCharacter.differentiable_LFunction (Finset.mem_filter.mp hχ).2.2).continuous
  have h_embed :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by
          filter_upwards [self_mem_nhdsWithin] with s hs h
          exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta : Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp h_embed
  have h_lprod : Filter.Tendsto (fun s : ℝ => evenLProduct p (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (evenLProduct p 1)) :=
    (h_cont.tendsto 1).comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_prod := h_zeta.mul h_lprod
  rw [one_mul] at h_prod
  refine (Filter.tendsto_congr' ?_).mp h_prod
  filter_upwards [self_mem_nhdsWithin] with s _
  ring

end KummerCriterion
