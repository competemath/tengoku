import Tengoku.Twinprime.TwinPrime.Analytic.MixedPrimeBetaSmallPart
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeDistribution
import Tengoku.Twinprime.TwinPrime.Analytic.TotientReciprocal
import Tengoku.Twinprime.TwinPrime.Sieve.TwinSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A Selberg upper sieve inside a prime-divisor progression

The support consists of multiples of a fixed prime `q` in the actual dyadic
interval, weighted by `Λ(n+2)`. Sifting below `q` gives the ordinary reciprocal
totient density. Its remainder is the actual progression error at `q*d`.
-/

noncomputable section

open Finset ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.omega

namespace TwinPrime.Analytic

open TwinPrime.Sieve

/-- The shifted-prime sieve restricted to multiples of `q`. The restriction
`z < q` is needed for the remainder formula, not to define the sieve.-/
def middlePrimeSieve (q X z : ℕ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Ioc X (2 * X)).filter (q ∣ ·)
  prodPrimes := oddPrimorial z
  prodPrimes_squarefree := oddPrimorial_squarefree z
  weights := fun n => vonMangoldt (n + 2)
  weights_nonneg := fun n => vonMangoldt_nonneg
  totalMass := (X : ℝ) / Nat.totient q
  nu := reciprocalTotient
  nu_mult := isMultiplicative_reciprocalTotient
  nu_pos_of_prime := fun p hp _ => by
    change 0 < 1 / (Nat.totient p : ℝ)
    exact one_div_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hp.pos)
  nu_lt_one_of_prime := fun p hp hpP => by
    change 1 / (Nat.totient p : ℝ) < 1
    have hp3 := three_le_of_prime_dvd_oddPrimorial hp hpP
    have ht : (1 : ℝ) < Nat.totient p := by
      rw [Nat.totient_prime hp]
      exact_mod_cast (show 1 < p - 1 by omega)
    exact (div_lt_one (lt_trans zero_lt_one ht)).mpr ht
  level := (z : ℝ) ^ 2
  one_le_level := by
    have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
    nlinarith

theorem prime_coprime_of_dvd_oddPrimorial (q z d : ℕ) (hq : q.Prime)
    (hzq : z < q) (hd : d ∣ oddPrimorial z) : q.Coprime d := by
  apply hq.coprime_iff_not_dvd.mpr
  intro hqd
  exact (not_lt_of_ge ((prime_dvd_oddPrimorial_iff hq).mp (hqd.trans hd)).2) hzq

theorem middlePrimeSieve_multSum (q X z d : ℕ) (hz : 1 ≤ z)
    (hqd : q.Coprime d) :
    (middlePrimeSieve q X z hz).multSum d =
      ∑ n ∈ Ioc X (2 * X) with q * d ∣ n, vonMangoldt (n + 2) := by
  simp only [multSum, middlePrimeSieve, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hq : q ∣ n <;> by_cases hd : d ∣ n
  · simp [hq, hd, hqd.mul_dvd_of_dvd_of_dvd hq hd]
  · have h : ¬q * d ∣ n := fun h => hd (dvd_of_mul_left_dvd h)
    simp [hq, hd, h]
  · have h : ¬q * d ∣ n := fun h => hq (dvd_of_mul_right_dvd h)
    simp [hq, h]
  · have h : ¬q * d ∣ n := fun h => hq (dvd_of_mul_right_dvd h)
    simp [hq, h]

/-- Inputs whose complete `W`-smooth part is the single prime `q`.-/
def middlePrimeInputs (q W X : ℕ) : Finset ℕ := by
  classical
  exact ((Ioc X (2 * X)).filter (q ∣ ·)).filter
    (fun n => ∀ p, p.Prime → p ∣ n / q → W < p)

/-- The positive mass whose negative is the middle-prime contribution.-/
def middlePrimeSlice (q W X : ℕ) : ℝ :=
  ∑ n ∈ middlePrimeInputs q W X, vonMangoldt (n + 2) * primeVaughanBeta W (n / q)

theorem middlePrimeSlice_nonneg (q W X : ℕ) : 0 ≤ middlePrimeSlice q W X :=
  sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (primeVaughanBeta_nonneg W (n / q))

theorem coprime_oddPrimorial_of_middlePrimeInputs (q W X z n : ℕ)
    (hq : q.Prime) (hzq : z < q) (hzW : z ≤ W)
    (hn : n ∈ middlePrimeInputs q W X) : (oddPrimorial z).Coprime n := by
  classical
  obtain ⟨hnbase, hrough⟩ := mem_filter.mp hn
  have hqn := (mem_filter.mp hnbase).2
  apply Nat.coprime_of_dvd'
  intro p hp hpP hpn
  have hpz := ((prime_dvd_oddPrimorial_iff hp).mp hpP).2
  have hpq : ¬p ∣ q := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    omega
  have hpn' : p ∣ q * (n / q) := by simpa only [Nat.mul_div_cancel' hqn] using hpn
  have hpquot := (hp.dvd_or_dvd hpn').resolve_left hpq
  exact False.elim ((not_lt_of_ge (hpz.trans hzW)) (hrough p hp hpquot))

/-- The whole beta-weighted class is bounded by the enlarged sifted set.
The quotient need not be prime, semiprime, or squarefree.-/
theorem middlePrimeSlice_le_siftedSum (q W X z : ℕ) (hz : 1 ≤ z)
    (hq : q.Prime) (hzq : z < q) (hzW : z ≤ W) (hqX : q ≤ 2 * X) :
    middlePrimeSlice q W X ≤ Real.log ((2 * X : ℝ) / q) *
      (middlePrimeSieve q X z hz).siftedSum := by
  classical
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hL : 0 ≤ Real.log ((2 * X : ℝ) / q) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hqpos).mpr
    simpa only [one_mul] using (show (q : ℝ) ≤ 2 * X by exact_mod_cast hqX)
  unfold middlePrimeSlice middlePrimeInputs
  rw [sum_filter]
  change _ ≤ Real.log ((2 * X : ℝ) / q) *
    ∑ n ∈ (Ioc X (2 * X)).filter (q ∣ ·),
      if (oddPrimorial z).Coprime n then vonMangoldt (n + 2) else 0
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  obtain ⟨hnI, hqn⟩ := mem_filter.mp hn
  by_cases hrough : ∀ p, p.Prime → p ∣ n / q → W < p
  · have hninput : n ∈ middlePrimeInputs q W X :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨hnI, hqn⟩, hrough⟩
    rw [ite_eq_left hrough, ite_eq_left (coprime_oddPrimorial_of_middlePrimeInputs
      q W X z n hq hzq hzW hninput)]
    have hnpos : 0 < n := (Nat.zero_le X).trans_lt (mem_Ioc.mp hnI).1
    have hbpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hnpos hqn) hq.pos
    have hble : ((n / q : ℕ) : ℝ) ≤ (2 * X : ℝ) / q := by
      apply (le_div_iff₀ hqpos).mpr
      exact_mod_cast (show n / q * q ≤ 2 * X by
        rw [Nat.div_mul_cancel hqn]
        exact (mem_Ioc.mp hnI).2)
    have hbeta := (primeVaughanBeta_le W (n / q)).trans
      ((vaughanBeta_le_log W (n / q)).trans
        (Real.log_le_log (by exact_mod_cast hbpos) hble))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbeta
      (vonMangoldt_nonneg (n := n + 2))
  · rw [ite_eq_right hrough]
    exact mul_nonneg hL (by split_ifs <;> positivity)

/-- The grouped Vaughan coefficient has exactly the claimed negative mass
on this class; this does not assert a bound for its complement.-/
theorem middlePrimeSlice_eq_neg_bilinear (U q W X : ℕ)
    (hU : 1 ≤ U) (hq : q.Prime) (hUq : U < q) (hqW : q ≤ W) :
    (∑ n ∈ middlePrimeInputs q W X,
      vonMangoldt (n + 2) * (moebiusHigh U * primeVaughanBeta W) n) =
      -middlePrimeSlice q W X := by
  classical
  rw [middlePrimeSlice, ← sum_neg_distrib]
  apply sum_congr rfl
  intro n hn
  obtain ⟨hnbase, hrough⟩ := mem_filter.mp hn
  obtain ⟨hnI, hqn⟩ := mem_filter.mp hnbase
  have hnpos : 0 < n := (Nat.zero_le X).trans_lt (mem_Ioc.mp hnI).1
  have hbpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hnpos hqn) hq.pos
  have hcoeff := primeVaughanBilinear_eq_neg_primeBeta_of_middle_prime
    U W q (n / q) hU hq hUq hqW hbpos hrough
  rw [Nat.mul_div_cancel' hqn] at hcoeff
  rw [hcoeff]
  ring

/-- Two different primes cannot both be the complete smooth part.-/
theorem middlePrimeInputs_disjoint (q r W X : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hrW : r ≤ W) (hqr : q ≠ r) :
    Disjoint (middlePrimeInputs q W X) (middlePrimeInputs r W X) := by
  classical
  apply disjoint_left.mpr
  intro n hnq hnr
  obtain ⟨hnbase, hrough⟩ := mem_filter.mp hnq
  have hqn := (mem_filter.mp hnbase).2
  have hrn := (mem_filter.mp (mem_filter.mp hnr).1).2
  have hrn' : r ∣ q * (n / q) := by simpa only [Nat.mul_div_cancel' hqn] using hrn
  rcases hr.dvd_or_dvd hrn' with hrq | hrquot
  · exact hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp hrq).symm
  · exact (not_lt_of_ge hrW) (hrough r hr hrquot)

/-- The complete mass over prime smooth parts in the cutoff band.-/
def middlePrimeMass (U W X : ℕ) : ℝ :=
  ∑ q ∈ Ioc U W with q.Prime, middlePrimeSlice q W X

theorem middlePrimeMass_nonneg (U W X : ℕ) : 0 ≤ middlePrimeMass U W X :=
  sum_nonneg fun q _ => middlePrimeSlice_nonneg q W X

end TwinPrime.Analytic
