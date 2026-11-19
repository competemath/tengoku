/-
Products of distinct natural prime bases and their use as positive integer codes.
New implementation source; not compiled in the assistant environment.
This module has no analytic or positive-window assumptions.
-/
import Tengoku.Erdos647.Erdos647Sieve.Specification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- Positive modulus encoded by a finite set of prime bases.-/
def primeSubsetProduct (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

private theorem natPrime_as_prime {p : ℕ} (hp : p.Prime) : Prime p := by
  refine ⟨hp.ne_zero, ?_, ?_⟩
  · simpa only [Nat.isUnit_iff] using hp.ne_one
  · intro a b h
    exact hp.dvd_mul.mp h

theorem primeSubsetProduct_pos (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) : 0 < primeSubsetProduct S := by
  unfold primeSubsetProduct
  exact Finset.prod_pos (fun p hp => (hS p hp).pos)

theorem selected_subset_product_pos (H : ℕ) (y : ℝ) (S : Finset ℕ)
    (hS : S ⊆ selectedPrimes H y) : 0 < primeSubsetProduct S := by
  apply primeSubsetProduct_pos
  intro p hp
  have hm : p ∈ (Finset.Icc (H + 1) (Nat.floor y)).filter Nat.Prime := hS hp
  exact (Finset.mem_filter.mp hm).2

/-- A prime divides a product of prime bases precisely when it is one of them.-/
theorem prime_dvd_primeSubsetProduct_iff_mem (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) (p : ℕ) (hp : p.Prime) :
    p ∣ primeSubsetProduct S ↔ p ∈ S := by
  constructor
  · intro hd
    obtain ⟨q, hq, hpq⟩ := (natPrime_as_prime hp).exists_mem_finset_dvd hd
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp hpq
    simpa only [heq] using hq
  · intro hm
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hm

/-- Unique prime bases give an injective subset-to-modulus encoding.-/
theorem primeSubsetProduct_injective (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (hprod : primeSubsetProduct S = primeSubsetProduct T) : S = T := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    apply (prime_dvd_primeSubsetProduct_iff_mem T hT p (hS p hp)).mp
    rw [← hprod]
    exact (prime_dvd_primeSubsetProduct_iff_mem S hS p (hS p hp)).mpr hp
  · intro hp
    apply (prime_dvd_primeSubsetProduct_iff_mem S hS p (hT p hp)).mp
    rw [hprod]
    exact (prime_dvd_primeSubsetProduct_iff_mem T hT p (hT p hp)).mpr hp

/-- Simultaneous prime divisibility equals divisibility by the product, even for
negative integers and zero. The product of the empty subset is one.-/
theorem primeSubsetProduct_int_dvd_iff (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (m : ℤ) :
    (primeSubsetProduct S : ℤ) ∣ m ↔ ∀ p ∈ S, (p : ℤ) ∣ m := by
  constructor
  · intro h p hp
    have hd : p ∣ primeSubsetProduct S :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
    have hdz : (p : ℤ) ∣ (primeSubsetProduct S : ℤ) := by exact_mod_cast hd
    exact hdz.trans h
  · intro h
    have hn : ∀ p ∈ S, p ∣ m.natAbs := by
      intro p hp
      have hz : (p : ℤ) ∣ (m.natAbs : ℤ) := by
        simpa only [Int.dvd_natAbs] using h p hp
      exact Int.natCast_dvd_natCast.mp hz
    have hd : primeSubsetProduct S ∣ m.natAbs :=
      Finset.prod_primes_dvd (s := S) m.natAbs (fun p hp => natPrime_as_prime (hS p hp)) hn
    have hz : (primeSubsetProduct S : ℤ) ∣ (m.natAbs : ℤ) := by exact_mod_cast hd
    simpa only [Int.dvd_natAbs] using hz

/-- A family of prime subsets with products in [1,M] has at most M elements.
This finite coding bound is one input to the later uniform remainder estimate.-/
theorem card_primeSubsetFamily_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset (Finset ℕ)) (hF : ∀ S ∈ F, S ⊆ P) (M : ℕ)
    (hM : ∀ S ∈ F, primeSubsetProduct S ≤ M) : F.card ≤ M := by
  classical
  have hcard : F.card ≤ (Finset.Icc 1 M).card := by
    apply Finset.card_le_card_of_injOn primeSubsetProduct
    · intro S hS
      exact Finset.mem_Icc.mpr
        ⟨primeSubsetProduct_pos S (fun p hp => hP p (hF S hS hp)), hM S hS⟩
    · intro S hS T hT hEq
      exact primeSubsetProduct_injective S T
        (fun p hp => hP p (hF S hS hp))
        (fun p hp => hP p (hF T hT hp)) hEq
  simpa using hcard

end Erdos647Sieve
end
