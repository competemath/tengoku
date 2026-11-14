import Tengoku.Twinprime.TwinPrime.Analytic.Vaughan
import Tengoku.Seed.Data.Nat.Totient
import Tengoku.Seed.Data.Nat.Prime.Int
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact odd Möbius/totient main-term identities

The finite Type I main term is not the product of its separate divisor sums:
shared prime factors contribute a correction. This file proves that correction
without any estimate for primes in progressions or any cancellation hypothesis.
All integer summations have positive inputs, and all divisions are in `ℝ`.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- Positive odd integers at most `U`.-/
def oddCutoff (U : ℕ) : Finset ℕ := (Icc 1 U).filter Odd

/-- `F(U) = ∑_{d≤U, d odd} μ(d)/φ(d)`.-/
def oddMoebiusTotientSum (U : ℕ) : ℝ :=
  ∑ d ∈ oddCutoff U, (μ d : ℝ) / Nat.totient d

/-- `F_p(U)`, the portion of `F(U)` with `p ∣ d`.-/
def oddMoebiusTotientSumDivisible (U p : ℕ) : ℝ :=
  ∑ d ∈ (oddCutoff U).filter (p ∣ ·), (μ d : ℝ) / Nat.totient d

/-- The exact finite Type I main term `Q(U,V)`.-/
def totientTypeIMain (U V : ℕ) : ℝ :=
  ∑ d ∈ oddCutoff U, ∑ b ∈ oddCutoff V,
    (μ d : ℝ) * vonMangoldt b / Nat.totient (d * b)

/-- Multiplication by powers of an existing prime factor scales the totient
by those powers. No squarefree hypothesis is needed.
@isnad1 id=eq.2h3v.s5.2633f86e58d3 from=translated src=- shape=6c9e38a5 vocab=0bb7b7b8
-/
theorem totient_mul_prime_pow_of_dvd {p d : ℕ} (hp : p.Prime) (hpd : p ∣ d)
    (k : ℕ) : Nat.totient (d * p ^ k) = Nat.totient d * p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show d * p ^ (k + 1) = p * (d * p ^ k) by ring,
      Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_left hpd _), ih]
    ring

/-- The reciprocal-totient correction for a positive prime power.
@isnad1 id=eq.2h3v.s7.bd64505983e5 from=translated src=- shape=e2ba0e81 vocab=7bc0f4cd
-/
theorem reciprocal_totient_mul_prime_pow (p d k : ℕ) (hp : p.Prime) (hd : 0 < d) :
    (1 : ℝ) / Nat.totient (d * p ^ (k + 1)) =
      1 / ((Nat.totient d : ℝ) * Nat.totient (p ^ (k + 1))) -
      if p ∣ d then
        1 / ((p : ℝ) * Nat.totient d * Nat.totient (p ^ (k + 1))) else 0 := by
  by_cases hpd : p ∣ d
  · have hφ : (Nat.totient d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hd).ne'
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith
    rw [ite_eq_left hpd, totient_mul_prime_pow_of_dvd hp hpd,
      Nat.totient_prime_pow_succ hp]
    push_cast [Nat.cast_sub hp.one_le]
    field_simp
    ring
  · have hcop : d.Coprime (p ^ (k + 1)) :=
      ((hp.coprime_iff_not_dvd.mpr hpd).symm).pow_right _
    rw [ite_eq_right hpd, sub_zero, Nat.totient_mul hcop, Nat.cast_mul]

/-- The shared-prime correction at a single summand. `minFac b` matters only
on the prime-power support of `Λ`; all other inputs contribute zero.
@isnad1 id=eq.1h2v.s8.718fe87cd329 from=translated src=- shape=5acc8cce vocab=924b22d2
-/
theorem moebius_mangoldt_totient_mul (d b : ℕ) (hd : 0 < d) :
    (μ d : ℝ) * vonMangoldt b / Nat.totient (d * b) =
      ((μ d : ℝ) / Nat.totient d) * (vonMangoldt b / Nat.totient b) -
      (if b.minFac ∣ d then (μ d : ℝ) / Nat.totient d else 0) *
        (vonMangoldt b / ((b.minFac : ℝ) * Nat.totient b)) := by
  by_cases hb : IsPrimePow b
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff b).mp hb
    cases k with
    | zero => omega
    | succ k =>
      rw [hp.pow_minFac (Nat.succ_ne_zero _)]
      have h := reciprocal_totient_mul_prime_pow p d k hp hd
      calc
        _ = (μ d : ℝ) * vonMangoldt (p ^ (k + 1)) *
            (1 / (Nat.totient (d * p ^ (k + 1)) : ℝ)) := by ring
        _ = _ := by
          rw [h]
          split_ifs <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
  · rw [vonMangoldt_eq_zero_iff.mpr hb]
    simp

/-- Formula (Q), with its prime powers indexed by their value `b`.
The correction has a minus sign and the additional factor `1 / minFac b`.
Because `Λ(b)=0` off prime powers, this is exactly the correction over `p^k≤V`.
No cancellation estimate is assumed.
@isnad1 id=eq.0h2v.s6.9e33853d35a2 from=translated src=- shape=6193dde3 vocab=9faa06ee
-/
theorem totientTypeIMain_eq_sharedPrimeCorrection (U V : ℕ) :
    totientTypeIMain U V =
      oddMoebiusTotientSum U *
        (∑ b ∈ oddCutoff V, vonMangoldt b / Nat.totient b) -
      ∑ b ∈ oddCutoff V,
        (vonMangoldt b / ((b.minFac : ℝ) * Nat.totient b)) *
          oddMoebiusTotientSumDivisible U b.minFac := by
  unfold totientTypeIMain
  calc
    _ = ∑ d ∈ oddCutoff U, ∑ b ∈ oddCutoff V,
        (((μ d : ℝ) / Nat.totient d) * (vonMangoldt b / Nat.totient b) -
        (if b.minFac ∣ d then (μ d : ℝ) / Nat.totient d else 0) *
          (vonMangoldt b / ((b.minFac : ℝ) * Nat.totient b))) := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro b _
      have hdpos : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
      exact moebius_mangoldt_totient_mul d b hdpos
    _ = _ := by
      simp only [sum_sub_distrib]
      congr 1
      · simp only [oddMoebiusTotientSum, sum_mul, mul_sum]
        rw [sum_comm]
      · rw [sum_comm]
        apply sum_congr rfl
        intro b _
        rw [← sum_mul, mul_comm]
        simp only [oddMoebiusTotientSumDivisible, sum_filter]

/-- The Möbius/totient summand after adjoining one prime. Repeated prime
factors give zero, as required in the recurrence for `F_p`.
@isnad1 id=eq.1h2v.s7.2cb736ad0884 from=translated src=- shape=01a40996 vocab=3edc5a08
-/
theorem moebiusTotient_mul_prime (p d : ℕ) (hp : p.Prime) :
    (μ (p * d) : ℝ) / Nat.totient (p * d) =
      if p ∣ d then 0 else -((μ d : ℝ) / Nat.totient d) / ((p : ℝ) - 1) := by
  by_cases hpd : p ∣ d
  · have hsq : ¬Squarefree (p * d) := by
      intro h
      exact (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul h)) hpd
    simp [hpd, moebius_eq_zero_of_not_squarefree hsq]
  · rw [ite_eq_right hpd,
      isMultiplicative_moebius.map_mul_of_coprime (hp.coprime_iff_not_dvd.mpr hpd),
      moebius_apply_prime hp, Nat.totient_mul_of_prime_of_not_dvd hp hpd]
    push_cast [Nat.cast_sub hp.one_le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Reindexing the multiples of an odd positive integer inside the odd cutoff.
@isnad1 id=eq.2h2v.s5.3954bc377ae7 from=translated src=- shape=dc722d76 vocab=d81dd18f
-/
theorem oddCutoff_filter_dvd_eq_image (U p : ℕ) (hp : 0 < p) (hpodd : Odd p) :
    (oddCutoff U).filter (p ∣ ·) =
      (oddCutoff (U / p)).image (fun d => p * d) := by
  ext d
  simp only [oddCutoff, mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨⟨hdpos, hdU⟩, hdodd⟩, ⟨e, rfl⟩⟩
    refine ⟨e, ⟨⟨?_, ?_⟩, Nat.Odd.of_mul_right hdodd⟩, rfl⟩
    · by_contra he
      have he0 : e = 0 := by omega
      simp [he0] at hdpos
    · exact (Nat.le_div_iff_mul_le hp).mpr (by simpa [mul_comm] using hdU)
  · rintro ⟨e, ⟨⟨hepos, heU⟩, heodd⟩, rfl⟩
    refine ⟨⟨⟨Nat.mul_pos hp hepos, ?_⟩, hpodd.mul heodd⟩, dvd_mul_right _ _⟩
    exact (by simpa [mul_comm] using (Nat.le_div_iff_mul_le hp).mp heU)

/--
@isnad1 id=eq.2h2v.s6.91cdbc1c0b97 from=translated src=- shape=51e51a63 vocab=5e0db16d
-/
theorem oddMoebiusTotientSumDivisible_eq_sum_mul (U p : ℕ) (hp : 0 < p)
    (hpodd : Odd p) :
    oddMoebiusTotientSumDivisible U p =
      ∑ d ∈ oddCutoff (U / p), (μ (p * d) : ℝ) / Nat.totient (p * d) := by
  unfold oddMoebiusTotientSumDivisible
  rw [oddCutoff_filter_dvd_eq_image U p hp hpodd,
    sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp hab)]

/-- The exact recurrence in PLAN.md, Section 6.3. Here `U / p` is the natural
cutoff: summing integers at most the real ratio gives precisely that cutoff.
@isnad1 id=eq.2h2v.s6.fec6368f7ce4 from=translated src=- shape=4258da89 vocab=53db2186
-/
theorem oddMoebiusTotientSumDivisible_recurrence (U p : ℕ) (hp : p.Prime)
    (hpodd : Odd p) :
    oddMoebiusTotientSumDivisible U p =
      -(oddMoebiusTotientSum (U / p) - oddMoebiusTotientSumDivisible (U / p) p) /
        ((p : ℝ) - 1) := by
  rw [oddMoebiusTotientSumDivisible_eq_sum_mul U p hp.pos hpodd]
  simp_rw [moebiusTotient_mul_prime p _ hp]
  unfold oddMoebiusTotientSum oddMoebiusTotientSumDivisible
  rw [sum_filter, ← sum_sub_distrib, ← sum_neg_distrib]
  simp only [div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro d _
  by_cases hd : p ∣ d <;> simp [hd]

/-- All odd prime powers at most `V`, indexed uniquely by `(prime, exponent)`.
The redundant finite bounds `p,k≤V` make the summation domain explicit.-/
def oddPrimePowerPairs (V : ℕ) : Finset (ℕ × ℕ) :=
  (((Icc 1 V).filter (fun p => p.Prime ∧ Odd p)) ×ˢ Icc 1 V).filter
    (fun pk => pk.1 ^ pk.2 ≤ V)

/-- Unique prime-power factorization justifies the finite reindexing.
@isnad1 id=eq.0h3v.s6.5aa6f4cdd032 from=translated src=- shape=ec77bfc7 vocab=895255d6
-/
theorem sum_odd_primePowers_eq {R : Type*} [AddCommMonoid R] (V : ℕ) (f : ℕ → R) :
    (∑ b ∈ (oddCutoff V).filter IsPrimePow, f b) =
      ∑ pk ∈ oddPrimePowerPairs V, f (pk.1 ^ pk.2) := by
  refine (sum_bij (i := fun pk _ => pk.1 ^ pk.2) ?_ ?_ ?_ ?_).symm
  · rintro ⟨p, k⟩ hpk
    simp only [oddPrimePowerPairs, mem_filter, mem_product, mem_Icc] at hpk
    obtain ⟨⟨⟨⟨_, _⟩, hp, hpodd⟩, hk, _⟩, hpkV⟩ := hpk
    simp only [oddCutoff, mem_filter, mem_Icc]
    exact ⟨⟨⟨pow_pos hp.pos _, hpkV⟩, hpodd.pow⟩, hp.isPrimePow.pow (by omega)⟩
  · rintro ⟨p, k⟩ hpk ⟨q, j⟩ hqj heq
    simp only [oddPrimePowerPairs, mem_filter, mem_product, mem_Icc] at hpk hqj
    have hp := hpk.1.1.2.1
    have hq := hqj.1.1.2.1
    have hk : k ≠ 0 := by have := hpk.1.2.1; omega
    have hj : j ≠ 0 := by have := hqj.1.2.1; omega
    exact Prod.ext (hp.pow_inj' hq hk hj heq).1 (hp.pow_inj' hq hk hj heq).2
  · intro b hb
    simp only [oddCutoff, mem_filter, mem_Icc] at hb
    obtain ⟨⟨⟨_, hbV⟩, hbodd⟩, hbpow⟩ := hb
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff b).mp hbpow
    refine ⟨(p, k), ?_, rfl⟩
    simp only [oddPrimePowerPairs, mem_filter, mem_product, mem_Icc]
    exact ⟨⟨⟨⟨hp.pos, (Nat.le_pow hk).trans hbV⟩, hp,
      (Nat.odd_pow_iff hk.ne').mp hbodd⟩,
      hk, (Nat.lt_pow_self hp.one_lt).le.trans hbV⟩, hbV⟩
  · intro pk _
    rfl

/-- Formula (Q) in its explicit prime/exponent form. Every odd prime power
`p^k≤V`, `k≥1`, appears exactly once in the correction.
@isnad1 id=eq.0h2v.s7.76ccf9fa72c3 from=translated src=- shape=f7ba6f50 vocab=2a7872cd
-/
theorem totientTypeIMain_eq_primePowerCorrection (U V : ℕ) :
    totientTypeIMain U V =
      oddMoebiusTotientSum U *
        (∑ b ∈ oddCutoff V, vonMangoldt b / Nat.totient b) -
      ∑ pk ∈ oddPrimePowerPairs V,
        (Real.log pk.1 / ((pk.1 : ℝ) * Nat.totient (pk.1 ^ pk.2))) *
          oddMoebiusTotientSumDivisible U pk.1 := by
  rw [totientTypeIMain_eq_sharedPrimeCorrection]
  congr 1
  let f : ℕ → ℝ := fun b =>
    (vonMangoldt b / ((b.minFac : ℝ) * Nat.totient b)) *
      oddMoebiusTotientSumDivisible U b.minFac
  have hfilter : (∑ b ∈ oddCutoff V, f b) =
      ∑ b ∈ (oddCutoff V).filter IsPrimePow, f b := by
    rw [sum_filter]
    apply sum_congr rfl
    intro b _
    by_cases hb : IsPrimePow b
    · simp [hb]
    · simp [hb, f, vonMangoldt_eq_zero_iff.mpr hb]
  change (∑ b ∈ oddCutoff V, f b) = _
  rw [hfilter, sum_odd_primePowers_eq]
  apply sum_congr rfl
  intro pk hpk
  simp only [oddPrimePowerPairs, mem_filter, mem_product, mem_Icc] at hpk
  have hp := hpk.1.1.2.1
  have hk : pk.2 ≠ 0 := by have := hpk.1.2.1; omega
  dsimp only [f]
  rw [hp.pow_minFac hk, vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp]

end TwinPrime.Analytic
