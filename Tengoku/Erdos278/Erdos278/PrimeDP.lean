import Tengoku.Erdos278.Erdos278.DPOptimization
import Tengoku.Erdos278.Erdos278.DPBounds
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- A canonical finite radix family proves that the DP theorem applies to every
positive input. This existence construction does not claim fast factorization.-/
def inputPrimes {r : ℕ} (n : Fin r → ℕ) : Finset ℕ :=
  univ.biUnion (fun i => (n i).primeFactors)

def inputPrimeRadix {r : ℕ} (n : Fin r → ℕ) (p : inputPrimes n) : ℕ := p.val

def inputPrimeExponents {r : ℕ} (n : Fin r → ℕ)
    (i : Fin r) (p : inputPrimes n) : ℕ := (n i).factorization p.val

/--
@isnad1 id=prime.0h3v.s4.143ef4426afa from=translated src=- shape=78535a9e vocab=68947f4b
-/
theorem input_radix_prime {r : ℕ} (n : Fin r → ℕ) (p : inputPrimes n) :
    (inputPrimeRadix n p).Prime := by
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp p.2
  exact Nat.prime_of_mem_primeFactors hi

/--
@isnad1 id=pairwise.0h2v.s6.cfc2e70ec87c from=translated src=- shape=98c735a0 vocab=5362a598
-/
theorem input_radices_coprime {r : ℕ} (n : Fin r → ℕ) :
    Pairwise (fun p q => (inputPrimeRadix n p).Coprime (inputPrimeRadix n q)) := by
  intro p q hpq
  apply (Nat.coprime_primes (input_radix_prime n p) (input_radix_prime n q)).mpr
  exact fun h => hpq (Subtype.ext h)

/--
@isnad1 id=eq.1h3v.s5.4d31f24fb670 from=translated src=- shape=60d05049 vocab=ce62846c
-/
theorem input_radix_representation {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) (i : Fin r) :
    radixModulus (inputPrimeRadix n) (inputPrimeExponents n i) = n i := by
  rw [radix_modulus_eq_product _ _ (input_radices_coprime n)]
  change (∏ p : inputPrimes n, p.val ^ (n i).factorization p.val) = n i
  rw [Finset.univ_eq_attach, Finset.prod_attach (inputPrimes n)
    (fun p => p ^ (n i).factorization p)]
  have hsub : (n i).primeFactors ⊆ inputPrimes n :=
    fun p hp => mem_biUnion.mpr ⟨i, mem_univ i, hp⟩
  have heq := Finset.prod_subset (f := fun p => p ^ (n i).factorization p) hsub
    (fun p _ hp => by
      have hz : (n i).factorization p = 0 := Finsupp.notMem_support_iff.mp hp
      simp [hz])
  rw [← heq]
  exact (Nat.prod_primeFactors_pow_factorization (hn i).ne').symm

noncomputable def primeDP {r : ℕ} (n : Fin r → ℕ) : Finset (SeparationMask r) :=
  radixDP (inputPrimeRadix n) (inputPrimeExponents n)

/-- Unconditional equality of all DP and original density values for every
nonempty positive input, including repeated moduli and modulus one.
@isnad1 id=iff.2h3v.s6.58836738b8df from=translated src=- shape=74efcb8a vocab=c0a455e1
-/
theorem prime_dp_density_exact {r : ℕ} (hr : 0 < r)
    (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) (d : ℚ) :
    (∃ H ∈ primeDP n, maskDensity n H = d) ↔
      ∃ a : Fin r → ℤ, density univ n a = d :=
  radix_dp_density_exact hr n _ _ (fun p => (input_radix_prime n p).pos)
    (input_radices_coprime n) (input_radix_representation n hn) d

/--
@isnad1 id=ex.2h2v.s7.27b9ee181fb0 from=translated src=- shape=6ff80ddf vocab=0b62f83f
-/
theorem prime_dp_maximum {r : ℕ} (hr : 0 < r)
    (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) :
    ∃ H ∈ primeDP n, ∃ a : Fin r → ℤ,
      maskDensity n H = density univ n a ∧
      (∀ K ∈ primeDP n, maskDensity n K ≤ maskDensity n H) ∧
      (∀ x : Fin r → ℤ, density univ n x ≤ density univ n a) :=
  radix_dp_maximum hr n _ _ (fun p => (input_radix_prime n p).pos)
    (input_radices_coprime n) (input_radix_representation n hn)

/--
@isnad1 id=le.1h2v.s6.39e52b448931 from=translated src=- shape=f5508fbb vocab=63f847b9
-/
theorem prime_dp_coordinate_bound {r : ℕ}
    (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) :
    radixCoordinateCount (inputPrimeExponents n) ≤ ∑ i, Nat.clog 2 (n i) := by
  have h := radix_coordinate_count_le_bit_bound (inputPrimeRadix n) (inputPrimeExponents n)
    (fun p => (input_radix_prime n p).two_le) (input_radices_coprime n)
  simpa only [input_radix_representation n hn] using h

/--
@isnad1 id=eq.0h3v.s6.64c67900ece8 from=translated src=- shape=af6d973d vocab=4d5a82d5
-/
theorem radix_coordinate_card {r : ℕ} {β : Type*} [Fintype β]
    (e : Fin r → β → ℕ) :
    Fintype.card (RadixCoordinate e) = radixCoordinateCount e := by
  simp [RadixCoordinate, radixCoordinateCount]

/--
@isnad1 id=le.0h2v.s6.662516615e1b from=translated src=- shape=eb555cca vocab=d17173ea
-/
theorem prime_dp_state_bound {r : ℕ} (n : Fin r → ℕ) :
    (primeDP n).card ≤ 2 ^ (r * (r-1) / 2) := by
  simpa only [separation_mask_universe_card] using (primeDP n).card_le_univ

/-- Public DP entry point: an attained finite-state maximum is the largest
ordinary natural density for the original positive moduli.
@isnad1 id=ex.2h2v.s7.2d8dab9426fa from=translated src=- shape=0bfc31de vocab=0cc97b1a
-/
theorem verified_dp_maximum_density {r : ℕ} (hr : 0 < r)
    (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) :
    ∃ H ∈ primeDP n, ∃ a : Fin r → ℤ, ∃ d : ℚ,
      d = maskDensity n H ∧ d = density univ n a ∧
      Filter.Tendsto (fun N : ℕ => (Nat.count (CoveredNat univ n a) N : ℝ) / N)
        Filter.atTop (nhds (d : ℝ)) ∧
      (∀ K ∈ primeDP n, maskDensity n K ≤ d) ∧
      (∀ x : Fin r → ℤ, density univ n x ≤ d) := by
  obtain ⟨H, hH, a, ha, hmax, hglobal⟩ := prime_dp_maximum hr n hn
  refine ⟨H, hH, a, density univ n a, ha.symm, rfl,
    density_is_natural_density univ n (fun i _ => hn i) a, ?_, hglobal⟩
  simpa only [ha] using hmax

end Erdos278
