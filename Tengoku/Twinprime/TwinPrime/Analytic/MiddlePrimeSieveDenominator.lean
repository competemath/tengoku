import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The exact denominator of the middle-prime Selberg sieve

The denominator is independent of the outer progression and consists of
the odd squarefree integers at most the sieve threshold. This file proves
the finite identification only, without assuming its logarithmic asymptotic.
-/

noncomputable section

open Finset ArithmeticFunction BoundingSieve

namespace TwinPrime.Analytic

open TwinPrime.Sieve

/-- Every positive odd squarefree integer below the threshold divides its
odd primorial.
@isnad1 id=dvd.3h2v.s4.e2e0ea9c5e8a from=translated src=- shape=855766a0 vocab=16d4ab91
-/
theorem dvd_oddPrimorial_of_odd_squarefree_le (d z : ℕ)
    (hdodd : Odd d) (hdsq : Squarefree d) (hdz : d ≤ z) :
    d ∣ oddPrimorial z := by
  have hsub : d.primeFactors ⊆ (Nat.primesLE z).erase 2 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    refine mem_erase.mpr ⟨?_, Nat.mem_primesLE.mpr ⟨?_, hpp⟩⟩
    · intro hp2
      subst p
      exact (Nat.not_even_iff_odd.mpr hdodd) (even_iff_two_dvd.mpr hpd)
    · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hdsq.ne_zero) hpd).trans hdz
  have hprod : (∏ p ∈ d.primeFactors, p) ∣
      ∏ p ∈ (Nat.primesLE z).erase 2, p :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsub
  simpa only [Nat.prod_primeFactors_of_squarefree hdsq, oddPrimorial] using hprod

/-- On its allowed divisors, the local Selberg term is exactly the product
of `1/(p-2)` over the distinct prime factors.
@isnad1 id=eq.2h4v.s6.055ea3cc20bb from=translated src=- shape=13fcfe83 vocab=cdf6c420
-/
theorem middlePrimeSieve_selbergTerms_eq (q X z d : ℕ) (hz : 1 ≤ z)
    (hd : d ∣ oddPrimorial z) :
    (middlePrimeSieve q X z hz).selbergTerms d =
      ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 2) := by
  rw [selbergTerms_apply, ← prod_primeFactors_nu hd, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hd
  have hp3 : (3 : ℝ) ≤ p := by
    exact_mod_cast three_le_of_prime_dvd_oddPrimorial hpp hpP
  change (1 / (Nat.totient p : ℝ)) * (1 - 1 / (Nat.totient p : ℝ))⁻¹ = _
  rw [Nat.totient_prime hpp, Nat.cast_sub hpp.one_le, Nat.cast_one]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have hdiff : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
    field_simp
    ring
  rw [hdiff, inv_div]
  field_simp

/-- The finite scalar denominator needed for the logarithmic main term.-/
def middlePrimeSelbergDenominator (z : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 z).filter (fun d => Odd d ∧ Squarefree d),
    ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 2)

/-- The Selberg cutoff `d²≤z²` selects precisely the odd squarefree
integers in `[1,z]`, including the contribution one at `d=1`.
@isnad1 id=eq.1h3v.s4.93a3db8ce43d from=translated src=- shape=9775eaa7 vocab=62d9aeb3
-/
theorem middlePrimeSieve_selbergBoundingSum_eq (q X z : ℕ) (hz : 1 ≤ z) :
    (middlePrimeSieve q X z hz).selbergBoundingSum =
      middlePrimeSelbergDenominator z := by
  classical
  have hset : (oddPrimorial z).divisors.filter
      (fun d : ℕ => (d : ℝ) ^ 2 ≤ (z : ℝ) ^ 2) =
      (Icc 1 z).filter (fun d : ℕ => Odd d ∧ Squarefree d) := by
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, hsq⟩
      have hdz : d ≤ z := by
        have hd0 : (0 : ℝ) ≤ d := by positivity
        have hz0 : (0 : ℝ) ≤ z := by positivity
        have : (d : ℝ) ≤ z := by nlinarith
        exact_mod_cast this
      have hdiv := Nat.dvd_of_mem_divisors hd
      have hdodd : Odd d := Nat.not_even_iff_odd.mp
        (fun h => not_two_dvd_of_dvd_oddPrimorial hdiv h.two_dvd)
      exact ⟨⟨Nat.pos_of_mem_divisors hd, hdz⟩, hdodd,
        (oddPrimorial_squarefree z).squarefree_of_dvd hdiv⟩
    · rintro ⟨⟨hdpos, hdz⟩, hdodd, hdsq⟩
      refine ⟨Nat.mem_divisors.mpr
        ⟨dvd_oddPrimorial_of_odd_squarefree_le d z hdodd hdsq hdz,
          oddPrimorial_ne_zero z⟩, ?_⟩
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdz) 2
  unfold SelbergSieve.selbergBoundingSum
  change (∑ d ∈ (oddPrimorial z).divisors,
    if (d : ℝ) ^ 2 ≤ (z : ℝ) ^ 2 then
      (middlePrimeSieve q X z hz).selbergTerms d else 0) = _
  rw [← sum_filter, hset]
  unfold middlePrimeSelbergDenominator
  apply sum_congr rfl
  intro d hd
  obtain ⟨hdI, hdodd, hdsq⟩ := mem_filter.mp hd
  exact middlePrimeSieve_selbergTerms_eq q X z d hz
    (dvd_oddPrimorial_of_odd_squarefree_le d z hdodd hdsq (mem_Icc.mp hdI).2)

/--
@isnad1 id=lt.1h1v.s4.3714256d6993 from=translated src=- shape=f8216502 vocab=32e52eec
-/
theorem middlePrimeSelbergDenominator_pos (z : ℕ) (hz : 1 ≤ z) :
    0 < middlePrimeSelbergDenominator z := by
  rw [← middlePrimeSieve_selbergBoundingSum_eq 1 0 z hz]
  exact SelbergSieve.selbergBoundingSum_pos _

end TwinPrime.Analytic
